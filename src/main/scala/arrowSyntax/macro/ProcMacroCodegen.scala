package arrowSyntax.`macro`

import scala.quoted.{Expr, Quotes, Type}

import cats.arrow.ArrowChoice

trait ProcMacroCodegen[F[_, _], A, B](using Type[F], Type[A], Type[B]):
  self: ProcMacro[F, A, B] =>
  import q.reflect.*
  import arrowSyntax.inlineSyntax.*

  private def abortOnTypeMatchFailure: Nothing = report.errorAndAbort("Failed to match on Type")

  private def withType[R](tpe: TypeRepr)(f: [T] => Unit => Type[T] ?=> R): R =
    tpe.asType match
      case '[t] => f[t](())
      case _    => abortOnTypeMatchFailure

  private def withTypes[R](tpe1: TypeRepr, tpe2: TypeRepr)(f: [T1, T2] => Unit => (Type[T1], Type[T2]) ?=> R): R =
    (tpe1.asType, tpe2.asType) match
      case ('[t1], '[t2]) => f[t1, t2](())
      case _              => abortOnTypeMatchFailure

  private lazy val leftModule: Symbol       = Symbol.requiredModule("scala.util.Left")
  private lazy val rightModule: Symbol      = Symbol.requiredModule("scala.util.Right")
  private lazy val eitherTypeRepr: TypeRepr = TypeRepr.of[Either]

  private lazy val arrowChoiceTyCl: Option[Expr[ArrowChoice[F]]] = Expr.summon[ArrowChoice[F]]

  def eitherType(leaves: Seq[TypeRepr]): TypeRepr = eitherTree(leaves)._2

  private def eitherTree(leaves: Seq[TypeRepr]): (Seq[Term => Term], TypeRepr) =
    if leaves.isEmpty then report.errorAndAbort("Cannot build an Either tree with no leaves")

    foldBalanced(leaves)(tpe => (Seq(identity[Term]), tpe)):
      case ((lInjs, lTpe), (rInjs, rTpe)) =>
        def wrap(module: Symbol)(t: Term): Term =
          Select
            .unique(Ref(module), "apply")
            .appliedToTypes(List(lTpe, rTpe))
            .appliedTo(t)

        (
          lInjs.map(_.andThen(wrap(leftModule)))
            ++ rInjs.map(_.andThen(wrap(rightModule))),
          eitherTypeRepr.appliedTo(List(lTpe, rTpe))
        )
  end eitherTree

  case class BuildState(arrow: Option[Term], storage: Storage)

  private class StepStorages(val old: Storage, prev: PatBinder, keep: Set[Symbol]):
    val prevBinder: Storage                                          = Storage.fromPat(prev)
    val combined: Storage.CombinedStorage[old.type, prevBinder.type] = old.addStorage(prevBinder)
    val kept: Storage.FilteredStorage[combined.type]                 = combined.filter(keep.contains)

  private def widenArrowRight[In: Type, Out: Type](arrow: Expr[F[In, Out]])[Target: Type]: Expr[F[In, Target]] =
    Type.of[Out] match
      case '[type out <: Target; out] =>
        if TypeRepr.of[out] =:= TypeRepr.of[Target] then arrow.asExprOf[F[In, Target]]
        else '{ ${ arrow.asExprOf[F[In, out]] }.rightWiden[Target](using $arrowTyCl) }
      case _ =>
        report.errorAndAbort(
          s"Type mismatch: ${Type.show[Out]} is not a subtype of ${Type.show[Target]}",
          arrow.asTerm.pos
        )
  end widenArrowRight

  private def handleCommand[Target: Type](cmd: Command): Term = cmd match
    case cmd: Command.InvokeArrow[from, to] =>
      given Type[from] = cmd.fromType
      given Type[to]   = cmd.toType

      widenArrowRight(cmd.arrow)[Target].asTerm
    case Command.If(cond, left, right) =>
      val arrowChoice = arrowChoiceTyCl
        .getOrElse(report.errorAndAbort(s"ArrowChoice[${Type.show[F]}] not found", cond.asTerm.pos))

      withTypes(left.inputType, right.inputType)([leftFrom, rightFrom] =>
        _ =>
          '{
            $arrowChoice.choice[leftFrom, rightFrom, Target](
              ${ handleCommand[Target](left).asExprOf[F[leftFrom, Target]] },
              ${ handleCommand[Target](right).asExprOf[F[rightFrom, Target]] }
            )
          }.asTerm
      )

    case Command.Match(on, cases) =>
      val arrowChoice = arrowChoiceTyCl
        .getOrElse(report.errorAndAbort(s"ArrowChoice[${Type.show[F]}] not found", on.pos))

      val (arrow, _) = foldBalanced(cases.map(_.thenDo))(cse => (handleCommand[Target](cse), cse.inputType)):
        case ((leftArrow, leftTpe), (rightArrow, rightTpe)) =>
          withTypes(leftTpe, rightTpe)([leftFrom, rightFrom] =>
            _ =>
              (
                '{
                  $arrowChoice.choice[leftFrom, rightFrom, Target](
                    ${ leftArrow.asExprOf[F[leftFrom, Target]] },
                    ${ rightArrow.asExprOf[F[rightFrom, Target]] }
                  )
                }.asTerm,
                TypeRepr.of[Either[leftFrom, rightFrom]]
              )
          )

      arrow
  end handleCommand

  private def executeCmd[Target: Type](state: BuildState, cmd: Command): BuildState =
    val cmdArrow = handleCommand[Target](cmd)

    withTypes(cmd.inputType, state.storage.makeType)([from, storageTupleType] =>
      _ =>
        val arrow =
          if state.storage.isEmpty then cmdArrow
          else '{ $arrowTyCl.first[from, Target, storageTupleType](${ cmdArrow.asExprOf[F[from, Target]] }) }.asTerm

        val newArrow = state.arrow match
          case Some(prevArrow) =>
            val inType  = state.storage.makePairType(TypeRepr.of[from])
            val outType = state.storage.makePairType(TypeRepr.of[Target])

            withTypes(inType, outType)([in, out] =>
              _ =>
                '{ ${ prevArrow.asExprOf[F[A, in]] }.andThen(${ arrow.asExprOf[F[in, out]] })(using $arrowTyCl) }.asTerm
            )
          case None => arrow

        BuildState(Some(newArrow), state.storage)
    )
  end executeCmd

  private def cmdToInput(
      cmd: Command,
      cmdStorage: Storage,
      cmdSymbols: cmdStorage.Symbols,
      ownerSymbol: Symbol
  ): Term =
    cmd match
      case cmd: Command.InvokeArrow[_, _] =>
        cmdStorage.remap(cmd.input.asTerm, cmdSymbols, ownerSymbol)
      case Command.If(cond, left, right) =>
        val leftInput    = cmdToInput(left, cmdStorage, cmdSymbols, ownerSymbol)
        val rightInput   = cmdToInput(right, cmdStorage, cmdSymbols, ownerSymbol)
        val remappedCond = cmdStorage.remap(cond.asTerm, cmdSymbols, ownerSymbol).asExprOf[Boolean]

        withTypes(left.inputType, right.inputType)([left, right] =>
          _ =>
            '{
              if $remappedCond then Left(${ leftInput.asExprOf[left] })
              else Right(${ rightInput.asExprOf[right] })
            }.asTerm
        )

      case Command.Match(on, cases) =>
        val (injections, _) = eitherTree(cases.map(_.thenDo.inputType))

        val caseDefs = cases
          .zip(injections)
          .map: (cse, injection) =>
            val caseStorage   = Storage.fromPat(PatBinder(cse.value, on.tpe))
            val caseSymbols   = caseStorage.makeSymbols(ownerSymbol)
            val newCmdStorage = cmdStorage.addStorage(caseStorage)
            val newCmdSymbols = newCmdStorage.addSymbols(cmdSymbols, caseSymbols)

            val pat   = newCmdStorage.remap(cse.value, newCmdSymbols, ownerSymbol)
            val guard = cse.guard.map(g => newCmdStorage.remap(g, newCmdSymbols, ownerSymbol))
            val body  = cmdToInput(cse.thenDo, newCmdStorage, newCmdSymbols, ownerSymbol)

            CaseDef(pat, guard, injection(body))

        Match(cmdStorage.remap(on, cmdSymbols, ownerSymbol), caseDefs.toList)
  end cmdToInput

  private def isIdentityStep(prev: PatBinder, next: Next, storages: StepStorages): Boolean = prev.pat match
    case b @ Bind(_, Wildcard()) =>
      def isBinder(t: Term): Boolean = unwrapInlined(t) match
        case i @ Ident(_) => i.symbol == b.symbol
        case _            => false

      storages.old.entrySymbols == storages.kept.entrySymbols && (next match
        case Next.Cmd(cmd: Command.InvokeArrow[_, _]) => isBinder(cmd.input.asTerm) && prev.tpe =:= cmd.inputType
        case Next.Cmd(_)                              => false
        case Next.Yield(result)                       => isBinder(result) && prev.tpe =:= TypeRepr.of[B])
    case _ => false

  private def stepFunction(
      prev: PatBinder,
      next: Next,
      storages: StepStorages,
      inType: TypeRepr,
      outType: TypeRepr
  ): Term =
    Lambda(
      Symbol.spliceOwner,
      MethodType(List("t"))(_ => List(inType), _ => outType),
      {
        case (sym, List(tuple: Term)) =>
          given Quotes = sym.asQuotes

          val prevBinderSymbols = storages.prevBinder.makeSymbols(sym)
          val oldSymbols        = storages.old.makeSymbols(sym)
          val combinedSymbols   = storages.combined.addSymbols(oldSymbols, prevBinderSymbols)
          val keptSymbols       = storages.kept.filterSymbols(combinedSymbols)

          val pat = storages.old.makePairUnapply(
            storages.prevBinder.remap(prev.pat, prevBinderSymbols, sym),
            prev.tpe,
            oldSymbols
          )
          val body = next match
            case Next.Cmd(cmd) =>
              storages.kept.makePairTerm(
                cmdToInput(cmd, storages.combined, combinedSymbols, sym),
                cmd.inputType,
                keptSymbols
              )
            case Next.Yield(result) =>
              storages.combined.remap(result, combinedSymbols, sym)

          Match(tuple, List(CaseDef(pat, None, body)))
        case _ => report.errorAndAbort("Lambda tree was not term")
      }
    )
  end stepFunction

  private def prepareCommand(state: BuildState, prev: PatBinder, next: Next, keep: Set[Symbol]): BuildState =
    val storages = new StepStorages(state.storage, prev, keep)

    if isIdentityStep(prev, next, storages) then BuildState(state.arrow, storages.kept)
    else
      val inType  = storages.old.makePairType(prev.tpe)
      val outType = next match
        case Next.Cmd(cmd) => storages.kept.makePairType(cmd.inputType)
        case Next.Yield(_) => TypeRepr.of[B]

      val lam = stepFunction(prev, next, storages, inType, outType)

      val arrow = withTypes(inType, outType)([in, out] =>
        _ =>
          val f = lam.asExprOf[in => out]
          state.arrow match
            case Some(prevArrow) => '{ ${ prevArrow.asExprOf[F[A, in]] }.rmap[out]($f)(using $arrowTyCl) }.asTerm
            case None            => '{ $arrowTyCl.lift[in, out]($f) }.asTerm
      )

      BuildState(Some(arrow), storages.kept)
  end prepareCommand

  def commandToTerm(state: BuildState, cmdPhase: CommandPhase): BuildState = cmdPhase match
    case CommandPhase.Execute(cmd, targetType) =>
      withType(targetType)([target] => _ => executeCmd[target](state, cmd))

    case CommandPhase.Prepare(prev, next, keep) => prepareCommand(state, prev, next, keep)
  end commandToTerm
