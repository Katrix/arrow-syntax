package arrowSyntax.`macro`

import scala.annotation.tailrec
import scala.quoted.{Expr, Type}

import arrowSyntax.ArrowSyntax
import cats.arrow.Arrow

trait ProcMacroParse[F[_, _], A, B](using Type[F]):
  self: ProcMacro[F, A, B] =>
  import q.reflect.*

  case class PatBinder(pat: Tree, tpe: TypeRepr)

  object Binder:
    def unapply(lam: Term): Option[(PatBinder, Term, Symbol)] = lam match
      case Lambda(List(valDef @ ValDef(_, typeTree, None)), Match(term, List(CaseDef(pat, None, next))))
          if valDef.symbol == term.symbol =>
        Some((PatBinder(pat, typeTree.tpe), next, valDef.symbol.owner))
      case UntupledLambda(valDef, params, body) =>
        val bindSyms = params.map(p => Symbol.newBind(Symbol.spliceOwner, p.name, Flags.EmptyFlags, p.tpt.tpe))
        val pat      = Unapply(
          TypeApply(
            Select.unique(Ref(defn.TupleClass(params.length).companionModule), "unapply"),
            params.map(p => Inferred(p.tpt.tpe))
          ),
          Nil,
          bindSyms.map(s => Bind(s, Wildcard()))
        )

        Some(
          (
            PatBinder(pat, valDef.tpt.tpe),
            replaceRefs(body, params.map(_.symbol).zip(bindSyms).toMap, valDef.symbol.owner),
            valDef.symbol.owner
          )
        )
      case Lambda(List(valDef @ ValDef(name, typeTree, None)), next) =>
        // Bind requires a symbol with the Case flag, so we can't reuse the parameter symbol directly
        val bindSym = Symbol.newBind(Symbol.spliceOwner, name, Flags.EmptyFlags, typeTree.tpe)

        Some(
          (
            PatBinder(Bind(bindSym, Wildcard()), typeTree.tpe),
            replaceRefs(next, Map(valDef.symbol -> bindSym), valDef.symbol.owner),
            valDef.symbol.owner
          )
        )
      case _ => None

    private def replaceRefs(term: Term, mapping: Map[Symbol, Symbol], owner: Symbol): Term =
      new TreeMap:
        override def transformTerm(tree: Term)(owner: Symbol): Term = tree match
          case Ident(_) if mapping.contains(tree.symbol) => Ref(mapping(tree.symbol))
          case _                                         => super.transformTerm(tree)(owner)
      .transformTerm(term)(owner)

    private object UntupledLambda:
      def unapply(lam: Term): Option[(ValDef, List[ValDef], Term)] = lam match
        case Lambda(List(valDef @ ValDef(_, typeTree, None)), Block(stats, expr)) =>
          val tpe   = typeTree.tpe.dealias
          val arity = tpe.typeArgs.length

          def isSelector(rhs: Term, i: Int): Boolean = unwrapInlined(rhs) match
            case Select(id @ Ident(_), sel) => id.symbol == valDef.symbol && sel == s"_${i + 1}"
            case _                          => false

          val (candidates, rest) = stats.splitAt(arity)
          val params             = candidates.zipWithIndex.collect:
            case (param @ ValDef(_, _, Some(rhs)), i) if isSelector(rhs, i) => param

          if arity >= 2 && defn.isTupleClass(tpe.typeSymbol) && params.length == arity then
            Some((valDef, params, if rest.isEmpty then expr else Block(rest, expr)))
          else None
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

    lazy val inputType: TypeRepr = this match
      case cmd: InvokeArrow[_, _] => TypeRepr.of(using cmd.fromType)
      case If(_, left, right)     => eitherType(Seq(left.inputType, right.inputType))
      case Match(_, cases)        => eitherType(cases.map(_.thenDo.inputType))

  enum Next:
    case Cmd(command: Command)
    case Yield(result: Term)

  enum CommandPhase:
    case Prepare(prev: PatBinder, next: Next, keep: Set[Symbol])
    case Execute(command: Command, targetType: TypeRepr)

  private def makeCommand(expr: Expr[Any]): Command = expr match
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

    case other =>
      other.asTerm match
        case Match(on, cases) =>
          val matchCases = cases.map:
            case CaseDef(value, guard, thenDo) =>
              MatchCase(value, guard, makeCommand(thenDo.asExpr))

          Command.Match(on, matchCases)
        case _ =>
          println(indentStructure(other.asTerm.show))
          report.errorAndAbort("Expected -< or -<< as flatMap/map recipient", expr.asTerm.pos)
  end makeCommand

  @tailrec
  private def collectCommands(term: Term, acc: List[CommandStep]): (Term, List[CommandStep]) = term match
    case Apply(TypeApply(Select(v, "flatMap"), _), List(Binder(binder, next, _))) =>
      collectCommands(next, CommandStep(makeCommand(v.asExpr), binder) :: acc)

    case Apply(TypeApply(Select(v, "map"), _), List(Binder(binder, rhs, _))) =>
      (rhs, (CommandStep(makeCommand(v.asExpr), binder) :: acc).reverse)
    case _ =>
      // A bare command (or a flatMap ending in one) is treated as `for r <- command yield r`
      val command    = makeCommand(term.asExpr)
      val resultType = term.tpe.widen.baseType(TypeRepr.of[ArrowSyntax].typeSymbol) match
        case AppliedType(_, List(_, res)) => res
        case _ => report.errorAndAbort("Expected for comprehension or arrow command", term.pos)
      val bindSym = Symbol.newBind(Symbol.spliceOwner, "r", Flags.EmptyFlags, resultType)
      val binder  = PatBinder(Bind(bindSym, Wildcard()), resultType)
      (Ref(bindSym), (CommandStep(command, binder) :: acc).reverse)
  end collectCommands

  def collectCommandPhase(forBody: Term, argBinder: PatBinder): List[CommandPhase] =
    val (lastMap, commands) = collectCommands(forBody, Nil)
    val usedFrom            = commands.map(c => commandUses(c.command)).scanRight(referencedSymbols(lastMap))(_ ++ _)
    val binders             = argBinder :: commands.map(_.binder)

    commands
      .lazyZip(binders)
      .lazyZip(usedFrom.tail)
      .flatMap: (curr, prevBinder, keep) =>
        Seq(
          CommandPhase.Prepare(prevBinder, Next.Cmd(curr.command), keep),
          CommandPhase.Execute(curr.command, curr.binder.tpe)
        )
      .appended(CommandPhase.Prepare(commands.last.binder, Next.Yield(lastMap), Set.empty))

  private def referencedSymbols(tree: Tree): Set[Symbol] =
    new TreeAccumulator[Set[Symbol]]:
      def foldTree(acc: Set[Symbol], tree: Tree)(owner: Symbol): Set[Symbol] = tree match
        case Ident(_) => acc + tree.symbol
        case _        => foldOverTree(acc, tree)(owner)
    .foldTree(Set.empty, tree)(Symbol.spliceOwner)

  private def commandUses(cmd: Command): Set[Symbol] = cmd match
    case cmd: Command.InvokeArrow[_, _] => referencedSymbols(cmd.input.asTerm)
    case Command.If(cond, left, right)  => referencedSymbols(cond.asTerm) ++ commandUses(left) ++ commandUses(right)
    case Command.Match(on, cases)       =>
      cases.foldLeft(referencedSymbols(on)): (acc, cse) =>
        acc ++ referencedSymbols(cse.value) ++ cse.guard.fold(Set.empty)(referencedSymbols) ++ commandUses(cse.thenDo)
