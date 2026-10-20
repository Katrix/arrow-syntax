package arrowSyntax.`macro`

import scala.annotation.tailrec
import scala.quoted.{Expr, Quotes, Type}

import arrowSyntax.ArrowSyntax
import cats.arrow.Arrow

class ProcMacro[F[_, _]: Type, A: Type, B: Type](val arrowTyCl: Expr[Arrow[F]])(
    using val q: Quotes
) extends ProcMacroStorage[F, A, B],
      ProcMacroParse[F, A, B],
      ProcMacroCodegen[F, A, B]:
  import q.reflect.*

  @tailrec
  final def unwrapInlined(term: Term): Term = term match
    case Inlined(_, _, t) => unwrapInlined(t)
    case r                => r

  def run(syntax: Expr[A => ArrowSyntax[F, B]]): Expr[F[A, B]] =
    given Printer[Tree] = Printer.TreeStructure

    val (argBinder, lambdaBody, lambdaOwner) = unwrapInlined(syntax.asTerm) match
      case Binder(binder, term, owner) => (binder, term, owner)
      case _ => report.errorAndAbort("Did not receive lambda as an argument, or got invalid lambda")

    val (preamble, forBody) = lambdaBody match
      case Block(pre, b) => (pre, b)
      case _             => (Nil, lambdaBody)

    val commandPhases = collectCommandPhase(forBody, argBinder)
    checkLiftable(argBinder, preamble, commandPhases, lambdaOwner)

    val arrowTerm = buildArrow(commandPhases, TypeRepr.of[A], TypeRepr.of[B])

    val res =
      if preamble.isEmpty then arrowTerm.asExprOf[F[A, B]]
      else Block(preamble, arrowTerm.changeOwner(lambdaOwner)).changeOwner(Symbol.spliceOwner).asExprOf[F[A, B]]

    println(res.asTerm.show(using Printer.TreeShortCode))

    res

  /**
    * The preamble and the arrows to the left of `-<` are hoisted out of the
    * proc lambda, so they are evaluated once when the arrow is built. They must
    * therefore not depend on anything bound inside the proc.
    */
  private def checkLiftable(
      argBinder: PatBinder,
      preamble: List[Statement],
      commandPhases: List[CommandPhase],
      lambdaOwner: Symbol
  ): Unit =
    val preambleSyms = preamble.collect { case d: Definition => d.symbol }.toSet
    val argSyms      = Binder.collectSymbolsAndTypes(argBinder).map(_._1).toSet

    // Includes the phases of rec blocks
    def allPhases(phases: List[CommandPhase]): List[CommandPhase] = phases.flatMap:
      case phase @ CommandPhase.Execute(cmd, _) => phase :: nestedPhases(cmd)
      case phase                                => List(phase)

    def nestedPhases(cmd: Command): List[CommandPhase] = cmd match
      case cmd: Command.Rec[_]        => allPhases(cmd.phases)
      case Command.If(_, left, right) => nestedPhases(left) ++ nestedPhases(right)
      case Command.Match(_, cases)    => cases.toList.flatMap(cse => nestedPhases(cse.thenDo))
      case _                          => Nil

    val phases = allPhases(commandPhases)

    // Binders created by the macro are owned by the splice owner, so they won't be found by checking ownership
    val binderSyms = phases
      .flatMap:
        case CommandPhase.Prepare(prev, _, _) => Binder.collectSymbolsAndTypes(prev).map(_._1)
        case _                                => Nil
      .toSet

    @tailrec
    def ownedByLambda(sym: Symbol): Boolean =
      val owner = sym.maybeOwner
      if owner == lambdaOwner then true
      else if owner.isNoSymbol || preambleSyms.contains(owner) then false
      else ownedByLambda(owner)

    def isProcLocal(sym: Symbol): Boolean =
      !preambleSyms.contains(sym) && (binderSyms.contains(sym) || ownedByLambda(sym))

    def localRefs(tree: Tree, isLocal: Symbol => Boolean): List[Tree] =
      new TreeAccumulator[List[Tree]]:
        def foldTree(acc: List[Tree], tree: Tree)(owner: Symbol): List[Tree] = tree match
          case Ident(_) if isLocal(tree.symbol) => tree :: acc
          case _                                => foldOverTree(acc, tree)(owner)
      .foldTree(Nil, tree)(Symbol.spliceOwner)
        .reverse

    def checkCommand(cmd: Command): List[Tree] = cmd match
      case cmd: Command.InvokeArrow[_, _] =>
        localRefs(cmd.arrow.asTerm, isProcLocal).map: ref =>
          report.error(
            s"The arrow cannot depend on `${ref.symbol.name}`, which is bound inside the proc. " +
              "Arrows to the left of -< are built once, before any input exists. " +
              "Use -<< to apply an arrow computed inside the proc",
            ref.pos
          )
          ref
      case _: Command.ApplyArrow[_, _] => Nil
      case _: Command.Rec[_]           => Nil // Checked through allPhases
      case Command.If(_, left, right) => checkCommand(left) ++ checkCommand(right)
      case Command.Match(_, cases)    => cases.toList.flatMap(cse => checkCommand(cse.thenDo))

    val commandErrors = phases.flatMap:
      case CommandPhase.Execute(cmd, _) => checkCommand(cmd)
      case _                            => Nil

    val preambleErrors = preamble.flatMap: stat =>
      localRefs(stat, argSyms.contains).map: ref =>
        report.error(
          s"Statements before the arrow commands cannot depend on the proc input `${ref.symbol.name}`",
          ref.pos
        )
        ref

    if commandErrors.nonEmpty || preambleErrors.nonEmpty then
      report.errorAndAbort("Proc contains arrows or statements that cannot be lifted out of the proc")
  end checkLiftable
