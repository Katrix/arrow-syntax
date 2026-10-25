package arrowSyntax.`macro`

import scala.annotation.tailrec
import scala.quoted.{Expr, Type}

import arrowSyntax.{ArrowLoop, ArrowSyntax, RecScope}
import cats.Eval
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
        val pat      = typedUnapply(
          TypeApply(
            Select.unique(Ref(defn.TupleClass(params.length).companionModule), "unapply"),
            params.map(p => Inferred(p.tpt.tpe))
          ),
          bindSyms.map(s => Bind(s, Wildcard())),
          valDef.tpt.tpe
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
    case ApplyArrow[A0, B0](fromType: Type[A0], toType: Type[B0], arrow: Expr[F[A0, B0]], input: Expr[A0])
        extends Command
    case If(cond: Expr[Boolean], left: Command, right: Command)
    case Match(on: Term, cases: Seq[MatchCase])

    /**
      * A rec block, built as a separate proc from `(env, Eval[feedback])` to
      * `(result, feedback)`, which is then closed using `loop`.
      */
    case Rec[R](
        resultType: Type[R],
        loop: Expr[ArrowLoop[F]],
        env: Storage,
        feedback: Storage,
        loopIn: TypeRepr,
        loopOut: TypeRepr,
        phases: List[CommandPhase]
    ) extends Command

    lazy val inputType: TypeRepr = this match
      case cmd: InvokeArrow[_, _]  => TypeRepr.of(using cmd.fromType)
      case cmd: ApplyArrow[a0, b0] =>
        given Type[a0] = cmd.fromType
        given Type[b0] = cmd.toType
        TypeRepr.of[(F[a0, b0], a0)]
      case If(_, left, right) => eitherType(Seq(left.inputType, right.inputType))
      case Match(_, cases)    => eitherType(cases.map(_.thenDo.inputType))
      case cmd: Rec[_]        => cmd.env.makeType

    /**
      * Maps the terms evaluated inside the proc, which excludes arrows to the
      * left of -<
      */
    def mapInputs(f: Term => Term): Command = this match
      case cmd: InvokeArrow[a, b] =>
        given Type[a] = cmd.fromType
        InvokeArrow(cmd.fromType, cmd.toType, cmd.arrow, f(cmd.input.asTerm).asExprOf[a])
      case cmd: ApplyArrow[a, b] =>
        given Type[a] = cmd.fromType
        given Type[b] = cmd.toType
        ApplyArrow(cmd.fromType, cmd.toType, f(cmd.arrow.asTerm).asExprOf[F[a, b]], f(cmd.input.asTerm).asExprOf[a])
      case If(cond, left, right) => If(f(cond.asTerm).asExprOf[Boolean], left.mapInputs(f), right.mapInputs(f))
      case Match(on, cases)      =>
        Match(f(on), cases.map(cse => cse.copy(guard = cse.guard.map(f), thenDo = cse.thenDo.mapInputs(f))))
      case cmd: Rec[_] => report.errorAndAbort("Cannot map the inputs of a rec block")

  enum Next:
    case Cmd(command: Command)
    case Yield(result: Term)

  enum CommandPhase:
    case Prepare(prev: PatBinder, next: Next, keep: Set[Symbol])
    case Execute(command: Command, targetType: TypeRepr)

  /**
    * @param inRec
    *   If we are inside a rec block, where -<# and -<<# are used instead of -<
    *   and -<<
    */
  private def makeCommand(expr: Expr[Any], inRec: Boolean = false): Command = expr match
    case '{ type a; arrowSyntax.-<[F, a, b]($arrow: F[a, b])($value: a)(using $ev: Arrow[F]) } if !inRec =>
      Command.InvokeArrow(
        Type.of[a],
        Type.of[b],
        arrow.asTerm
          .changeOwner(Symbol.spliceOwner)
          .asExprOf[F[a, b]],
        value
      )
    case '{ type a; arrowSyntax.-<[F, a, b](if $cond then $e1 else $e2)($value: a)(using $ev: Arrow[F]) } if !inRec =>
      Command.If(
        cond,
        Command.InvokeArrow(
          Type.of[a],
          Type.of[b],
          e1.asTerm
            .changeOwner(Symbol.spliceOwner)
            .asExprOf[F[a, b]],
          value
        ),
        Command.InvokeArrow(
          Type.of[a],
          Type.of[b],
          e2.asTerm
            .changeOwner(Symbol.spliceOwner)
            .asExprOf[F[a, b]],
          value
        )
      )

    case '{ type a; arrowSyntax.-<<[F, a, b]($arrow: F[a, b])($value: a)(using $ev: Arrow[F]) } if !inRec =>
      // The arrow is computed inside the proc, so unlike -< it is not hoisted out
      Command.ApplyArrow(Type.of[a], Type.of[b], arrow, value)

    case '{ type a; arrowSyntax.-<<[F, a, b](if $cond then $e1 else $e2)($value: a)(using $ev: Arrow[F]) } if !inRec =>
      Command.If(
        cond,
        Command.InvokeArrow(
          Type.of[a],
          Type.of[b],
          e1.asTerm
            .changeOwner(Symbol.spliceOwner)
            .asExprOf[F[a, b]],
          value
        ),
        Command.InvokeArrow(
          Type.of[a],
          Type.of[b],
          e2.asTerm
            .changeOwner(Symbol.spliceOwner)
            .asExprOf[F[a, b]],
          value
        )
      )  

    case '{ type a; arrowSyntax.-<#[F, a, b]($arrow: F[a, b])($value: a)(using $scope: RecScope[F]) } if inRec =>
      Command.InvokeArrow(
        Type.of[a],
        Type.of[b],
        arrow.asTerm
          .changeOwner(Symbol.spliceOwner)
          .asExprOf[F[a, b]],
        value
      )

    case '{ type a; arrowSyntax.-<<#[F, a, b]($arrow: F[a, b])($value: a)(using $scope: RecScope[F]) } if inRec =>
      Command.ApplyArrow(Type.of[a], Type.of[b], arrow, value)

    case '{ arrowSyntax.rec[F, r]($body)(using $loop: ArrowLoop[F]) } if !inRec =>
      makeRec[r](body.asTerm, loop)

    case '{ if $cond then $e1 else $e2 } =>
      Command.If(cond, makeCommand(e1, inRec), makeCommand(e2, inRec))
    case other =>
      other.asTerm match
        case Match(on, cases) =>
          val matchCases = cases.map:
            case CaseDef(value, guard, thenDo) =>
              MatchCase(value, guard, makeCommand(thenDo.asExpr, inRec))

          Command.Match(on, matchCases)
        case _ if inRec =>
          report.errorAndAbort("Expected -<# or -<<# as the right hand side of a val in rec", expr.asTerm.pos)
        case _ =>
          // println(indentStructure(other.asTerm.show))
          report.errorAndAbort("Expected -< or -<< as flatMap/map recipient", expr.asTerm.pos)
  end makeCommand

  private def containsSyntax(tree: Tree, names: Set[String]): Boolean =
    new TreeAccumulator[Boolean]:
      def foldTree(acc: Boolean, tree: Tree)(owner: Symbol): Boolean = acc || (tree match
        case _: Ident | _: Select
            if names.contains(tree.symbol.name) && tree.symbol.maybeOwner.fullName.startsWith("arrowSyntax") =>
          true
        case _ => foldOverTree(acc, tree)(owner))
    .foldTree(false, tree)(Symbol.spliceOwner)

  private def boundSymbols(tree: Tree): Set[Symbol] =
    new TreeAccumulator[Set[Symbol]]:
      def foldTree(acc: Set[Symbol], tree: Tree)(owner: Symbol): Set[Symbol] = tree match
        case b: Bind => foldOverTree(acc + b.symbol, tree)(owner)
        case _       => foldOverTree(acc, tree)(owner)
    .foldTree(Set.empty, tree)(Symbol.spliceOwner)

  private def makeRec[R: Type](body: Term, loop: Expr[ArrowLoop[F]]): Command =
    val (stats, result) = unwrapInlined(body) match
      case Lambda(List(_), Block(stats, expr)) => (stats, expr)
      case Lambda(List(_), expr)               => (Nil, expr)
      case _                                   => report.errorAndAbort("Expected a block as the body of rec", body.pos)

    val valDefs = stats.map:
      case v @ ValDef(_, _, Some(_)) => v
      case stat                      => report.errorAndAbort("Only vals can be defined in rec", stat.pos)
    if valDefs.isEmpty then report.errorAndAbort("rec must define at least one val", body.pos)

    val rhss  = valDefs.map(_.rhs.get)
    val index = valDefs.map(_.symbol).zipWithIndex.toMap
    val binds = valDefs.map(v => Symbol.newBind(Symbol.spliceOwner, v.name, Flags.EmptyFlags, v.tpt.tpe))

    def replaceVals(term: Term, owner: Symbol): Term =
      new TreeMap:
        override def transformTerm(tree: Term)(owner: Symbol): Term = tree match
          case Ident(_) if index.contains(tree.symbol) => Ref(binds(index(tree.symbol)))
          case _                                       => super.transformTerm(tree)(owner)
      .transformTerm(term)(owner)

    // A val referenced at or before its own definition is fed back through the loop
    val feedbackIdxs = rhss.zipWithIndex
      .flatMap((rhs, i) => referencedSymbols(rhs).toList.flatMap(index.get).filter(_ >= i))
      .distinct
      .sorted
    val feedback    = new Storage(feedbackIdxs.map(i => (sym = binds(i), tpe = valDefs(i).tpt.tpe)))
    val feedbackSym =
      Symbol.newBind(Symbol.spliceOwner, "feedback", Flags.EmptyFlags, TypeRepr.of[Eval].appliedTo(feedback.makeType))

    val recBindSet                                   = binds.zipWithIndex.toMap
    def readFeedback(defined: Int)(term: Term): Term =
      new TreeMap:
        override def transformTerm(tree: Term)(owner: Symbol): Term = tree match
          case Ident(_) if recBindSet.get(tree.symbol).exists(_ >= defined) =>
            feedback.makeSelect(
              Select.unique(Ref(feedbackSym), "value"),
              feedbackIdxs.indexOf(recBindSet(tree.symbol))
            )
          case _ => super.transformTerm(tree)(owner)
      .transformTerm(term)(Symbol.spliceOwner)

    val steps = valDefs
      .zip(rhss)
      .zipWithIndex
      .map:
        case ((valDef, rhs), i) =>
          val replaced = replaceVals(rhs, valDef.symbol)
          val command  =
            if containsSyntax(replaced, Set("-<#", "-<<#")) then makeCommand(replaced.asExpr, inRec = true)
            else if containsSyntax(replaced, Set("-<", "-<<", "rec")) then
              report.errorAndAbort("Use -<# and -<<# inside rec, not -< and -<<", rhs.pos)
            else
              // Plain vals are passed through the identity arrow
              valDef.tpt.tpe.asType match
                case '[t] => Command.InvokeArrow(Type.of[t], Type.of[t], '{ $arrowTyCl.id[t] }, replaced.asExprOf[t])

          CommandStep(command.mapInputs(readFeedback(i)), PatBinder(Bind(binds(i), Wildcard()), valDef.tpt.tpe))

    // The environment is everything bound outside the rec block that it uses
    val recTrees = rhss :+ result
    val inside   = recTrees.flatMap(boundSymbols).toSet
    val envSyms  = recTrees.flatMap(t => referencedSymbols(t).toList).distinct.filter(s => s.isBind && !inside(s))
    val env      = new Storage(envSyms.map(s => (sym = s, tpe = s.termRef.widen)))

    val loopIn    = TypeRepr.of[Tuple2].appliedTo(List(env.makeType, feedbackSym.termRef.widen))
    val loopOut   = TypeRepr.of[Tuple2].appliedTo(List(TypeRepr.of[R], feedback.makeType))
    val argBinder = PatBinder(
      typedUnapply(
        TypeApply(
          Select.unique(Ref(defn.TupleClass(2).companionModule), "unapply"),
          List(Inferred(env.makeType), Inferred(feedbackSym.termRef.widen))
        ),
        List(env.makeUnapply(env.entrySymbolsAsSymbols), Bind(feedbackSym, Wildcard())),
        loopIn
      ),
      loopIn
    )
    val yieldTerm = Select
      .unique(Ref(defn.TupleClass(2).companionModule), "apply")
      .appliedToTypes(List(TypeRepr.of[R], feedback.makeType))
      .appliedTo(replaceVals(result, Symbol.spliceOwner), feedback.makeTupleTerm(feedback.entrySymbolsAsSymbols))

    Command.Rec(Type.of[R], loop, env, feedback, loopIn, loopOut, phasesFor(argBinder, steps, yieldTerm))
  end makeRec

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
    phasesFor(argBinder, commands, lastMap)

  private def phasesFor(argBinder: PatBinder, commands: List[CommandStep], lastMap: Term): List[CommandPhase] =
    val usedFrom = commands.map(c => commandUses(c.command)).scanRight(referencedSymbols(lastMap))(_ ++ _)
    val binders  = argBinder :: commands.map(_.binder)

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
    case cmd: Command.ApplyArrow[_, _]  => referencedSymbols(cmd.arrow.asTerm) ++ referencedSymbols(cmd.input.asTerm)
    case Command.If(cond, left, right)  => referencedSymbols(cond.asTerm) ++ commandUses(left) ++ commandUses(right)
    case Command.Match(on, cases)       =>
      cases.foldLeft(referencedSymbols(on)): (acc, cse) =>
        acc ++ referencedSymbols(cse.value) ++ cse.guard.fold(Set.empty)(referencedSymbols) ++ commandUses(cse.thenDo)
    case cmd: Command.Rec[_] => cmd.env.entrySymbols.toSet
