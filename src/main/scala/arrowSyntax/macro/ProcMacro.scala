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

    // TODO: Verify that argBinder symbols are not used in preamble
    val (preamble, forBody) = lambdaBody match
      case Block(pre, b) => (pre, b)
      case _             => (Nil, lambdaBody)

    val commandPhases = collectCommandPhase(forBody, argBinder)
    val finalState    = commandPhases.foldLeft(BuildState(None, new Storage(Nil)))(commandToTerm)
    val arrowTerm     = finalState.arrow.getOrElse(report.errorAndAbort("Proc did not produce an arrow"))

    val res =
      if preamble.isEmpty then arrowTerm.asExprOf[F[A, B]]
      else Block(preamble, arrowTerm.changeOwner(lambdaOwner)).changeOwner(Symbol.spliceOwner).asExprOf[F[A, B]]

    println(res.asTerm.show(using Printer.TreeShortCode))

    res
