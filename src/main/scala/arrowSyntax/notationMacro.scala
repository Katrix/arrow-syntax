package arrowSyntax

import scala.annotation.tailrec
import scala.quoted.{Expr, Quotes, Type, Varargs}

import arrowSyntax.`macro`.ProcMacro
import cats.arrow.{Arrow, ArrowChoice}

def procImpl[F[_, _]: {Type}, A: Type, B: Type](syntax: Expr[A => ArrowSyntax[F, B]], arrowTyCl: Expr[Arrow[F]])(
    using q: Quotes
): Expr[F[A, B]] =
  import q.reflect.*

  new ProcMacro[F, A, B](arrowTyCl).run(syntax)

end procImpl
