package arrowSyntax.`macro`

import scala.quoted.{Expr, Quotes, Type}

import arrowSyntax.ArrowApply
import cats.Eval
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

  private def withTypes[R](tpe1: TypeRepr, tpe2: TypeRepr, tpe3: TypeRepr)(
      f: [T1, T2, T3] => Unit => (Type[T1], Type[T2], Type[T3]) ?=> R
  ): R =
    (tpe1.asType, tpe2.asType, tpe3.asType) match
      case ('[t1], '[t2], '[t3]) => f[t1, t2, t3](())
      case _                     => abortOnTypeMatchFailure

  private lazy val leftModule: Symbol       = Symbol.requiredModule("scala.util.Left")
  private lazy val rightModule: Symbol      = Symbol.requiredModule("scala.util.Right")
  private lazy val eitherTypeRepr: TypeRepr = TypeRepr.of[Either]

  private lazy val arrowChoiceTyCl: Option[Expr[ArrowChoice[F]]] = Expr.summon[ArrowChoice[F]]
  private lazy val arrowApplyTyCl: Option[Expr[ArrowApply[F]]]   = Expr.summon[ArrowApply[F]]

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

  /** @param procIn The input type of the arrow being built
    * @param procOut The output type of the arrow being built
    */
  case class BuildState(arrow: Option[Term], storage: Storage, procIn: TypeRepr, procOut: TypeRepr)

  def buildArrow(phases: List[CommandPhase], procIn: TypeRepr, procOut: TypeRepr): Term =
    phases
      .foldLeft(BuildState(None, new Storage(Nil), procIn, procOut))(commandToTerm)
      .arrow
      .getOrElse(report.errorAndAbort("Proc did not produce an arrow"))

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
    case cmd: Command.ApplyArrow[from, to] =>
      given Type[from] = cmd.fromType
      given Type[to]   = cmd.toType

      val arrowApply = arrowApplyTyCl
        .getOrElse(report.errorAndAbort(s"ArrowApply[${Type.show[F]}] not found", cmd.arrow.asTerm.pos))

      widenArrowRight('{ $arrowApply.app[from, to] })[Target].asTerm
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

    case cmd: Command.Rec[r] =>
      given Type[r] = cmd.resultType
      val inner     = buildArrow(cmd.phases, cmd.loopIn, cmd.loopOut)

      withTypes(cmd.env.makeType, cmd.feedback.makeType)([env, fb] =>
        _ =>
          val looped = '{ ${ cmd.loop }.loop[env, r, fb](${ inner.asExprOf[F[(env, Eval[fb]), (r, fb)]] }) }
          widenArrowRight(looped)[Target].asTerm
      )
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

            withTypes(state.procIn, inType, outType)([procIn, in, out] =>
              _ =>
                '{ ${ prevArrow.asExprOf[F[procIn, in]] }.andThen(${ arrow.asExprOf[F[in, out]] })(using $arrowTyCl) }.asTerm
            )
          case None => arrow

        state.copy(arrow = Some(newArrow))
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
      case cmd: Command.ApplyArrow[_, _] =>
        val arrow = cmdStorage.remap(cmd.arrow.asTerm, cmdSymbols, ownerSymbol)
        val input = cmdStorage.remap(cmd.input.asTerm, cmdSymbols, ownerSymbol)

        Select
          .unique(Ref(defn.TupleClass(2).companionModule), "apply")
          .appliedToTypes(cmd.inputType.typeArgs)
          .appliedTo(arrow, input)
      case Command.If(cond, left, right) =>
        val leftInput    = cmdToInput(left, cmdStorage, cmdSymbols, ownerSymbol)
        val rightInput   = cmdToInput(right, cmdStorage, cmdSymbols, ownerSymbol)
        val remappedCond = cmdStorage.remap(cond.asTerm, cmdSymbols, ownerSymbol)
        val (injections, _) = eitherTree(Seq(left.inputType, right.inputType))

        If(remappedCond, injections(0)(leftInput), injections(1)(rightInput))

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

      case cmd: Command.Rec[_] =>
        cmdStorage.remap(cmd.env.makeTupleTerm(cmd.env.entrySymbolsAsSymbols), cmdSymbols, ownerSymbol)
  end cmdToInput

  private def isIdentityStep(prev: PatBinder, next: Next, storages: StepStorages, procOut: TypeRepr): Boolean =
    prev.pat match
      case b @ Bind(_, Wildcard()) =>
        def isBinder(t: Term): Boolean = unwrapInlined(t) match
          case i @ Ident(_) => i.symbol == b.symbol
          case _            => false

        storages.old.entrySymbols == storages.kept.entrySymbols && (next match
          case Next.Cmd(cmd: Command.InvokeArrow[_, _]) => isBinder(cmd.input.asTerm) && prev.tpe =:= cmd.inputType
          case Next.Cmd(_)                              => false
          case Next.Yield(result)                       => isBinder(result) && prev.tpe =:= procOut)
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

          Match(uncheckedIfXXL(tuple, pat), List(CaseDef(pat, None, body)))
        case _ => report.errorAndAbort("Lambda tree was not term")
      }
    )
  end stepFunction

  private def prepareCommand(state: BuildState, prev: PatBinder, next: Next, keep: Set[Symbol]): BuildState =
    val storages = new StepStorages(state.storage, prev, keep)

    if isIdentityStep(prev, next, storages, state.procOut) then state.copy(storage = storages.kept)
    else
      val inType  = storages.old.makePairType(prev.tpe)
      val outType = next match
        case Next.Cmd(cmd) => storages.kept.makePairType(cmd.inputType)
        case Next.Yield(_) => state.procOut

      val lam = stepFunction(prev, next, storages, inType, outType)

      val arrow = withTypes(state.procIn, inType, outType)([procIn, in, out] =>
        _ =>
          val f = lam.asExprOf[in => out]
          state.arrow match
            case Some(prevArrow) => '{ ${ prevArrow.asExprOf[F[procIn, in]] }.rmap[out]($f)(using $arrowTyCl) }.asTerm
            case None            => '{ $arrowTyCl.lift[in, out]($f) }.asTerm
      )

      BuildState(Some(arrow), storages.kept, state.procIn, state.procOut)
  end prepareCommand

  def commandToTerm(state: BuildState, cmdPhase: CommandPhase): BuildState = cmdPhase match
    case CommandPhase.Execute(cmd, targetType) =>
      withType(targetType)([target] => _ => executeCmd[target](state, cmd))

    case CommandPhase.Prepare(prev, next, keep) => prepareCommand(state, prev, next, keep)
  end commandToTerm
