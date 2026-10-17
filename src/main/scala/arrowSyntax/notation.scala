package arrowSyntax

import scala.annotation.compileTimeOnly
import scala.quoted.Type

import cats.arrow.Arrow

@compileTimeOnly("ArrowSyntax was not removed by macro")
trait ArrowSyntax[F[_, _], A] {

  @compileTimeOnly("ArrowSyntax.map was not removed by macro")
  def map[C](f: A => C): ArrowSyntax[F, C]

  @compileTimeOnly("ArrowSyntax.flatMap was not removed by macro")
  def flatMap[C](f: A => ArrowSyntax[F, C]): ArrowSyntax[F, C]
}

extension [F[_, _]: Arrow, A, B](arr: F[A, B])
  @compileTimeOnly("-< was not removed by macro")
  def -<(a: A): ArrowSyntax[F, B] = sys.error("-< was not removed by macro")
  @compileTimeOnly("-<< was not removed by macro")
  def -<<(a: A): ArrowSyntax[F, B] = sys.error("-<< was not removed by macro")

class Syntax[A](private val b: Boolean) extends AnyVal:
  inline def proc[F[_, _]: {Arrow as arrow}, B](inline syntax: A => ArrowSyntax[F, B]): F[A, B] =
    ${ procImpl[F, A, B]('{ syntax }, '{ arrow }) }

// TODO: recursive

object arrows:
  inline def lift[F[_, _]](using arrow: Arrow[F])[A, B](f: A => B): F[A, B] = arrow.lift(f)

  inline def apply[A]: Syntax[A] = new Syntax[A](false)
