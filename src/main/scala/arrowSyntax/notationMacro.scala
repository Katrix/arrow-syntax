package arrowSyntax

import scala.annotation.tailrec
import scala.quoted.{Expr, Quotes, Type, Varargs}

import cats.arrow.{Arrow, ArrowChoice}

def indentStructure(s: String, step: String = "  "): String =
  val sb       = StringBuilder()
  var depth    = 0
  var inString = false
  var i        = 0

  def newline() = sb.append('\n').append(step * depth)

  while i < s.length do
    val c = s(i)
    if inString then
      sb.append(c)
      if c == '\\' && i + 1 < s.length then {
        sb.append(s(i + 1));
        i += 1
      } else if c == '"' then inString = false
    else
      c match
        case '"'                                        => inString = true; sb.append(c)
        case '(' if i + 1 < s.length && s(i + 1) == ')' => sb.append("()"); i += 1
        case '('                                        => depth += 1; sb.append('('); newline()
        case ')'                                        => depth -= 1; newline(); sb.append(')')
        case ','                                        =>
          sb.append(',');
          newline();
          if i + 1 < s.length && s(i + 1) == ' ' then
            i +=
              1
        case _ => sb.append(c)
    i += 1
  sb.toString

private def foldBalanced[L, N](leaves: Seq[L])(leaf: L => N)(node: (N, N) => N): N =
  require(leaves.nonEmpty, "Cannot fold an empty sequence")

  if leaves.length == 1 then leaf(leaves.head)
  else
    val (l, r) = leaves.splitAt(leaves.length / 2)
    node(foldBalanced(l)(leaf)(node), foldBalanced(r)(leaf)(node))

def procImpl[F[_, _]: {Type}, A: Type, B: Type](syntax: Expr[A => ArrowSyntax[F, B]], arrowTyCl: Expr[Arrow[F]])(
    using q: Quotes
): Expr[F[A, B]] =
  import q.reflect.*

  def abortOnTypeMatchFailure = report.errorAndAbort("Failed to match on Type")

  case class PatBinder(pat: Tree, tpe: TypeRepr)
  object Binder:
    def unapply(lam: Term): Option[(PatBinder, Term)] = lam match
      case Lambda(List(valDef @ ValDef(_, typeTree, None)), Match(term, List(CaseDef(pat, None, next))))
          if valDef.symbol == term.symbol =>
        Some((PatBinder(pat, typeTree.tpe), next))
      case Lambda(List(valDef @ ValDef(name, typeTree, None)), next) =>
        // Bind requires a symbol with the Case flag, so we can't reuse the parameter symbol directly
        val bindSym = Symbol.newBind(Symbol.spliceOwner, name, Flags.EmptyFlags, typeTree.tpe)
        val mapper  = new TreeMap:
          override def transformTerm(tree: Term)(owner: Symbol): Term = tree match
            case Ident(_) if tree.symbol == valDef.symbol => Ref(bindSym)
            case _                                        => super.transformTerm(tree)(owner)

        Some((PatBinder(Bind(bindSym, Wildcard()), typeTree.tpe), mapper.transformTerm(next)(valDef.symbol.owner)))
      case _ => None

    def collectSymbolsAndTypes(pat: PatBinder): List[(Symbol, TypeRepr)] =
      new TreeAccumulator[List[(Symbol, TypeRepr)]]:
        @tailrec
        def foldTree(acc: List[(Symbol, TypeRepr)], tree: Tree)(owner: Symbol): List[(Symbol, TypeRepr)] = tree match
          case b @ Bind(_, inner) => foldTree((b.symbol, b.symbol.termRef.widen) :: acc, inner)(owner)
          case _                  => foldOverTree(acc, tree)(owner)
      .foldTree(Nil, pat.pat)(Symbol.spliceOwner)
        .reverse

  case class MatchCase(value: Tree, guard: Option[Term], thenDo: Command)

  case class CommandStep(command: Command, binder: PatBinder)

  enum Command:
    case InvokeArrow[A0, B0](fromType: Type[A0], toType: Type[B0], arrow: Expr[F[A0, B0]], input: Expr[A0])
        extends Command
    case If(cond: Expr[Boolean], left: Command, right: Command)
    case Match(on: Term, cases: Seq[MatchCase])

  enum CommandPhase:
    case Prepare(prev: PatBinder, curr: Either[Command, Term])
    case Execute(command: Command, targetType: TypeRepr)

  def tupleCompanion(n: Int): Term = Ref(defn.TupleClass(n).companionModule)

  def tupleXXLCompanion: Term = Ref(Symbol.requiredModule("scala.runtime.TupleXXL"))

  def eitherTree(leaves: Seq[TypeRepr]): (Seq[Term => Term], TypeRepr) =
    if leaves.isEmpty then report.errorAndAbort("Cannot build an Either tree with no leaves")

    foldBalanced(leaves)(tpe => (Seq(identity[Term]), tpe)):
      case ((lInjs, lTpe), (rInjs, rTpe)) =>
        def wrap(module: String)(t: Term): Term =
          Select
            .unique(Ref(Symbol.requiredModule(module)), "apply")
            .appliedToTypes(List(lTpe, rTpe))
            .appliedTo(t)

        (
          lInjs.map(_.andThen(wrap("scala.util.Left")))
            ++ rInjs.map(_.andThen(wrap("scala.util.Right"))),
          TypeRepr.of[Either].appliedTo(List(lTpe, rTpe))
        )

  class Storage(
      private val entries: Seq[(sym: Symbol, tpe: TypeRepr)]
  ):
    opaque type Symbols = Seq[Symbol]

    private[Storage] def wrapSymbols(s: Seq[Symbol]): Symbols   = s
    private[Storage] def unwrapSymbols(s: Symbols): Seq[Symbol] = s

    private def isXXL: Boolean = entries.length > 22

    def makeSymbols(owner: Symbol): Symbols =
      entries.map(t => Symbol.newBind(owner, Symbol.freshName(t.sym.name), Flags.EmptyFlags, t.tpe))

    def makeUnapply(symbols: Symbols): Tree =
      if entries.isEmpty then Wildcard()
      else if isXXL then
        // TupleXXL elements are untyped, so we need a type test to give the binds their types
        val unchecked = '{ new scala.unchecked() }.asTerm
        Unapply(
          Select.unique(tupleXXLCompanion, "unapplySeq"),
          Nil,
          entries
            .zip(symbols)
            .map((t, s) => Bind(s, TypedOrTest(Wildcard(), Inferred(AnnotatedType(t.tpe, unchecked)))))
            .toList
        )
      else
        Unapply(
          TypeApply(
            Select.unique(tupleCompanion(entries.length), "unapply"),
            entries.map(t => Inferred(t.tpe)).toList
          ),
          Nil,
          symbols.map(s => Bind(s, Wildcard())).toList
        )

    def makeTupleTerm(symbols: Symbols): Term =
      if entries.isEmpty then Literal(UnitConstant())
      else if isXXL then '{ scala.runtime.TupleXXL(${ Varargs(symbols.map(s => Ref(s).asExpr)) }*) }.asTerm
      else
        TypeApply(
          Select.unique(tupleCompanion(entries.length), "apply"),
          entries.map(t => Inferred(t.tpe)).toList
        ).appliedToArgs(symbols.map(s => Ref(s)).toList)

    def makeType: TypeRepr =
      if entries.isEmpty then TypeRepr.of[Unit]
      else if isXXL then TypeRepr.of[scala.runtime.TupleXXL]
      else defn.TupleClass(entries.length).typeRef.appliedTo(entries.map(_.tpe).toList)

    def remap[T <: Tree](tree: T, newSymbols: Symbols, ownerSymbol: Symbol): T =
      val mapping = entries.map(_.sym).zip(newSymbols).toMap

      val mapper = new TreeMap:
        override def transformTerm(tree: Term)(owner: Symbol): Term = tree match
          case Ident(_) if mapping.contains(tree.symbol) => Ref(mapping(tree.symbol))
          case _                                         => super.transformTerm(tree)(owner)

        // TreeMap does not recurse into the pattern of a Bind, so we handle all Binds ourselves
        override def transformTree(tree: Tree)(owner: Symbol): Tree = tree match
          case b @ Bind(name, inner) =>
            Bind(mapping.getOrElse(b.symbol, b.symbol), transformTree(inner)(owner))
          case _ => super.transformTree(tree)(owner)

      mapper.transformTree(tree)(ownerSymbol) match
        case t: Term => t.changeOwner(ownerSymbol).asInstanceOf[T]
        case t       => t.asInstanceOf[T]

    def addStorage(storage: Storage): Storage.CombinedStorage[this.type, storage.type] =
      new Storage.CombinedStorage(this, storage)

  object Storage:
    class CombinedStorage[L <: Storage & scala.Singleton, R <: Storage & scala.Singleton](
        val left: L,
        val right: R
    ) extends Storage(left.entries ++ right.entries):
      def addSymbols(leftSymbols: left.Symbols, rightSymbols: right.Symbols): Symbols =
        wrapSymbols(left.unwrapSymbols(leftSymbols) ++ right.unwrapSymbols(rightSymbols))

    def fromPat(pat: PatBinder): Storage = new Storage(Binder.collectSymbolsAndTypes(pat))

  given Printer[Tree] = Printer.TreeStructure

  @tailrec
  def unwrapInlined(term: Term): Term = term match
    case Inlined(_, _, t) => unwrapInlined(t)
    case r                => r

  val (argBinder, lambdaBody) = unwrapInlined(syntax.asTerm) match
    case Binder(binder, term) => (binder, term)
    case _                    => report.errorAndAbort("Did not receive lambda as an argument, or got invalid lambda")

  // TODO: Veify that argBinder symbols are not used in preample
  val (preample, forBody) = lambdaBody match
    case Block(pre, b) => (pre, b)
    case _             => (Nil, lambdaBody)

  def makeCommand(expr: Expr[Any]): Command = expr match
    case '{ type a; arrowSyntax.-<[F, a, b]($arrow: F[a, b])($value: a)(using $ev: Arrow[F]) } =>
      Command.InvokeArrow(
        Type.of[a],
        Type.of[b],
        arrow.asTerm
          .changeOwner(Symbol.spliceOwner)
          .asExprOf[F[a, b]], // TODO: Verify that the arrow can be lifted out of the current context
        value
      )

    case '{ if $cond then $e1 else $e2 } =>
      Command.If(cond, makeCommand(e1), makeCommand(e2))

    case matchDef if matchDef.asTerm match
          case Match(on, cases) => true
          case _                => false
        =>

      matchDef.asTerm match {
        case Match(on, cases) =>
          val matchCases = cases.map:
            case CaseDef(value, guard, thenDo) =>
              MatchCase(value, guard, makeCommand(thenDo.asExpr))

          Command.Match(on, matchCases)
      }

    case other =>
      println(indentStructure(other.asTerm.show))
      report.errorAndAbort("Expected -< or -<< as flatMap/map recipient", expr.asTerm.pos)
  end makeCommand

  @tailrec
  def collectCommands(term: Term, acc: List[CommandStep]): (Term, List[CommandStep]) = term match
    case Apply(TypeApply(Select(v, "flatMap"), _), List(Binder(binder, next))) =>
      collectCommands(next, CommandStep(makeCommand(v.asExpr), binder) :: acc)

    case Apply(TypeApply(Select(v, "map"), _), List(Binder(binder, rhs))) =>
      (rhs, (CommandStep(makeCommand(v.asExpr), binder) :: acc).reverse)
    case _ => report.errorAndAbort("Expected for comprehension", term.pos)
  end collectCommands

  val (lastMap, commands) = collectCommands(forBody, Nil)
  val commandPhases       =
    val first   = commands.head
    val last    = commands.last
    val sliding = commands.sliding(2).flatMap {
      case List(prev, curr) =>
        Seq(CommandPhase.Prepare(prev.binder, Left(curr.command)), CommandPhase.Execute(curr.command, curr.binder.tpe))
      case _ => report.errorAndAbort("List.sliding is misbehaving")
    }

    Seq(CommandPhase.Execute(first.command, first.binder.tpe)) ++ sliding ++ Seq(
      CommandPhase.Prepare(last.binder, Right(lastMap))
    )
  end commandPhases

  import arrowSyntax.inlineSyntax.*

  case class CommandExecuteRes[From, To](arrow: Expr[F[From, To]], fromType: Type[From], toType: Type[To])

  def commandToTerm(
      acc: (res: Term, storage: Storage),
      cmdPhase: CommandPhase
  ): (res: Term, storage: Storage) = cmdPhase match
    case CommandPhase.Execute(cmd, targetType) =>
      targetType.asType match
        case '[target] =>
          def widen[In: Type, Out: Type](arrow: Expr[F[In, Out]]): Expr[F[In, target]] =
            Type.of[Out] match
              case '[type out <: target; out] =>
                if TypeRepr.of[out] =:= TypeRepr.of[target] then
                  arrow.asExprOf[F[In, target]]
                else
                  '{ ${ arrow.asExprOf[F[In, out]] }.rightWiden[target](using $arrowTyCl) }
              case _ =>
                report.errorAndAbort(
                  s"Type mismatch: ${Type.show[Out]} is not a subtype of ${Type.show[target]}",
                  arrow.asTerm.pos
                )

          def handleCommand(cmd: Command): CommandExecuteRes[?, target] = cmd match
            case cmd: Command.InvokeArrow[from, to] =>
              given Type[from] = cmd.fromType
              given Type[to]   = cmd.toType

              CommandExecuteRes(widen(cmd.arrow), cmd.fromType, Type.of[target])
            case Command.If(cond, left, right) =>
              (handleCommand(left), handleCommand(right)) match
                case (
                      leftRes: CommandExecuteRes[leftFrom, `target`],
                      rightRes: CommandExecuteRes[rightFrom, `target`]
                    ) =>
                  given Type[leftFrom]  = leftRes.fromType
                  given Type[rightFrom] = rightRes.fromType

                  val arrowChoiceTyCl = Expr
                    .summon[ArrowChoice[F]]
                    .getOrElse(report.errorAndAbort(s"ArrowChoice[${Type.show[F]}] not found", cond.asTerm.pos))

                  CommandExecuteRes(
                    '{
                      $arrowChoiceTyCl
                        .choice[leftFrom, rightFrom, target](${ leftRes.arrow }, ${ rightRes.arrow })
                    },
                    Type.of[Either[leftFrom, rightFrom]],
                    Type.of[target]
                  )

            case Command.Match(on, cases) =>
              val reses = cases.map(cse => handleCommand(cse.thenDo))

              val arrowChoiceTyCl = Expr
                .summon[ArrowChoice[F]]
                .getOrElse(report.errorAndAbort(s"ArrowChoice[${Type.show[F]}] not found", on.pos))

              foldBalanced(reses)(identity):
                case (
                      leftRes: CommandExecuteRes[leftFrom, `target`],
                      rightRes: CommandExecuteRes[rightFrom, `target`]
                    ) =>
                  given Type[leftFrom]  = leftRes.fromType
                  given Type[rightFrom] = rightRes.fromType

                  CommandExecuteRes(
                    '{
                      $arrowChoiceTyCl
                        .choice[leftFrom, rightFrom, target](${ leftRes.arrow }, ${ rightRes.arrow })
                    },
                    Type.of[Either[leftFrom, rightFrom]],
                    Type.of[target]
                  )
          end handleCommand

          (handleCommand(cmd), acc.storage.makeType.asType) match
            case (res: CommandExecuteRes[from, `target`], '[storageTupleType]) =>
              given Type[from] = res.fromType
              (
                '{
                  ${ acc.res.asExprOf[F[A, (from, storageTupleType)]] }.andThen(
                    $arrowTyCl.first[from, target, storageTupleType](${ res.arrow })
                  )(using $arrowTyCl)
                }.asTerm,
                acc.storage
              )
            case (_: CommandExecuteRes[from, `target`], _) => abortOnTypeMatchFailure

    case CommandPhase.Prepare(prev, curr) =>
      val oldStorage        = acc.storage
      val prevBinderStorage = Storage.fromPat(prev)
      val newStorage        = oldStorage.addStorage(prevBinderStorage)

      def makeFromType(cmd: Command): Type[?] = cmd match
        case cmd: Command.InvokeArrow[from, _] => cmd.fromType
        case Command.If(cond, left, right)     =>
          (makeFromType(left), makeFromType(right)) match
            case ('[left], '[right]) => Type.of[Either[left, right]]
            case _                   => abortOnTypeMatchFailure
        case Command.Match(on, cases) =>
          val leafTypes = cases.map: cse =>
            makeFromType(cse.thenDo) match
              case '[t] => TypeRepr.of[t]
              case _    => abortOnTypeMatchFailure

          eitherTree(leafTypes)._2.asType

      val fromTypeWithCmd = curr.left.map(c => (c, makeFromType(c)))
      val fromType        = fromTypeWithCmd.left.map(_._2)

      (prev.tpe.asType, oldStorage.makeType.asType, newStorage.makeType.asType) match
        case ('[mid2], '[storageTupleType], '[storageTupleResultType]) =>
          val lam = Lambda(
            Symbol.spliceOwner,
            MethodType(List("t"))(
              _ => List(TypeRepr.of[(mid2, storageTupleType)]),
              _ =>
                fromType match
                  case Left('[from]) => TypeRepr.of[(from, storageTupleResultType)]
                  case Right(_)      => TypeRepr.of[B]
                  case Left(_)       => abortOnTypeMatchFailure
            ),
            {
              case (sym, List(tuple: Term)) =>
                given Quotes = sym.asQuotes

                val prevBinderSymbols = prevBinderStorage.makeSymbols(sym)
                val oldSymbols        = oldStorage.makeSymbols(sym)
                val newSymbols        = newStorage.addSymbols(oldSymbols, prevBinderSymbols)

                def cmdToInput(cmd: Command, cmdStorage: Storage, cmdSymbols: cmdStorage.Symbols): (Term, TypeRepr) =
                  cmd match
                    case cmd: Command.InvokeArrow[from2, _] =>
                      (cmdStorage.remap(cmd.input.asTerm, cmdSymbols, sym), TypeRepr.of(using cmd.fromType))
                    case Command.If(cond, left, right) =>
                      val (leftInput, leftType)   = cmdToInput(left, cmdStorage, cmdSymbols)
                      val (rightInput, rightType) = cmdToInput(right, cmdStorage, cmdSymbols)
                      val remappedCond            = cmdStorage.remap(cond.asTerm, cmdSymbols, sym).asExprOf[Boolean]

                      (leftType.asType, rightType.asType) match
                        case ('[left], '[right]) =>
                          (
                            '{
                              if $remappedCond then Left(${ leftInput.asExprOf[left] })
                              else Right(${ rightInput.asExprOf[right] })
                            }.asTerm,
                            TypeRepr.of[Either[left, right]]
                          )
                        case (_, _) => abortOnTypeMatchFailure

                    case Command.Match(on, cases) =>
                      val caseDefParts = cases.map: cse =>
                        val caseStorage   = Storage.fromPat(PatBinder(cse.value, on.tpe))
                        val caseSymbols   = caseStorage.makeSymbols(sym)
                        val newCmdStorage = cmdStorage.addStorage(caseStorage)
                        val newCmdSymbols = newCmdStorage.addSymbols(cmdSymbols, caseSymbols)

                        val pat              = newCmdStorage.remap(cse.value, newCmdSymbols, sym)
                        val guard            = cse.guard.map(g => newCmdStorage.remap(g, newCmdSymbols, sym))
                        val (body, bodyType) = cmdToInput(cse.thenDo, newCmdStorage, newCmdSymbols)

                        (pat, guard, body, bodyType)

                      val (injections, eitherType) = eitherTree(caseDefParts.map(_._4))

                      val caseDefs = caseDefParts
                        .zip(injections)
                        .map:
                          case ((pat, guard, body, _), injection) => CaseDef(pat, guard, injection(body))

                      (
                        Match(
                          cmdStorage.remap(on, cmdSymbols, sym),
                          caseDefs.toList
                        ),
                        eitherType
                      )
                end cmdToInput

                Match(
                  tuple,
                  List(
                    CaseDef(
                      Unapply(
                        TypeApply(
                          Select.unique(tupleCompanion(2), "unapply"),
                          List(Inferred(TypeRepr.of[mid2]), Inferred(TypeRepr.of[storageTupleType]))
                        ),
                        Nil,
                        List(
                          prevBinderStorage.remap(prev.pat, prevBinderSymbols, sym),
                          oldStorage.makeUnapply(oldSymbols)
                        )
                      ),
                      None,
                      fromTypeWithCmd match
                        case Left((cmd, '[from])) =>
                          TypeApply(
                            Select.unique(tupleCompanion(2), "apply"),
                            List(Inferred(TypeRepr.of[from]), Inferred(TypeRepr.of[storageTupleResultType]))
                          ).appliedTo(cmdToInput(cmd, newStorage, newSymbols)._1, newStorage.makeTupleTerm(newSymbols))
                        case Right(map) =>
                          newStorage.remap(map, newSymbols, sym)
                        case Left(_) => abortOnTypeMatchFailure
                    )
                  )
                )
              case _ => report.errorAndAbort("Lambda tree was not term")
            }
          )

          val prevRes = acc.res.asExprOf[F[A, (mid2, storageTupleType)]]
          val res     = fromType match
            case Left('[from]) =>
              '{
                $prevRes.rmap[(from, storageTupleResultType)](${
                  lam.asExprOf[((mid2, storageTupleType)) => (from, storageTupleResultType)]
                })(using $arrowTyCl)
              }
            case Right(_) =>
              '{ $prevRes.rmap[B](${ lam.asExprOf[((mid2, storageTupleType)) => B] })(using $arrowTyCl) }
            case Left(_) => abortOnTypeMatchFailure

          (res.asTerm, newStorage)
        case (_, _, _) => abortOnTypeMatchFailure

  val freshStorage = new Storage(Nil)
  val startingTerm = freshStorage.makeType.asType match
    case '[storageTupleType] =>
      val lam = Lambda(
        Symbol.spliceOwner,
        MethodType(List("a"))(_ => List(TypeRepr.of[A]), _ => TypeRepr.of[(A, storageTupleType)]),
        {
          case (sym, List(term: Term)) =>
            given Quotes = sym.asQuotes

            val symbols = freshStorage.makeSymbols(sym)

            '{
              (
                ${ term.asExprOf[A] },
                ${ freshStorage.makeTupleTerm(symbols).asExprOf[storageTupleType] }
              )
            }.asTerm

          case _ => report.errorAndAbort("Lambda tree was not term")
        }
      )
      
      '{ $arrowTyCl.lift(${lam.asExprOf[A => (A, storageTupleType)]}) }.asTerm

  val firstPrepare = commandToTerm((startingTerm, freshStorage), CommandPhase.Prepare(argBinder, Left(commands.head.command)))

  val (arrowTerm, storage) =
    commandPhases.tail.foldLeft(commandToTerm(firstPrepare, commandPhases.head))(commandToTerm)

  val res = preample.headOption.map(_.symbol.owner) match
    case Some(lambdaOwner) =>
      Block(preample, arrowTerm.changeOwner(lambdaOwner)).changeOwner(Symbol.spliceOwner).asExprOf[F[A, B]]
    case None => arrowTerm.asExprOf[F[A, B]]

  println(res.asTerm.show(using Printer.TreeShortCode))

  res
end procImpl
