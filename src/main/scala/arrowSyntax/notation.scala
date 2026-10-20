package arrowSyntax

import scala.annotation.{compileTimeOnly, implicitNotFound}
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

extension [F[_, _], A, B](arr: F[A, B])
  @compileTimeOnly("-<# was not removed by macro")
  def -<#(a: A)(using RecScope[F]): B = sys.error("-<# was not removed by macro")
  @compileTimeOnly("-<<# was not removed by macro")
  def -<<#(a: A)(using RecScope[F]): B = sys.error("-<<# was not removed by macro")

@implicitNotFound("-<# and -<<# can only be used inside rec")
sealed trait RecScope[F[_, _]]

/**
  * A block of vals which may refer to vals defined later in the same block,
  * like `rec` in Haskell's arrow notation. Each val is either an arrow command
  * using `-<#` or `-<<#`, or a plain expression.
  *
  * {{{
  * for
  *   (y, z) <- rec {
  *     lazy val y: Int = f -<# (x, z)
  *     lazy val z: Int = g -<# y
  *     (y, z)
  *   }
  * yield y + z
  * }}}
  *
  * The vals are evaluated in order. A reference to a val defined at or after
  * the current one is fed back using [[ArrowLoop.loop]], and is only valid
  * once the whole block has been evaluated. Forcing it before then, for
  * example by passing it directly to a strict arrow, will not terminate. Such
  * references should only be used lazily, like inside a lambda or a by-name
  * argument, or with an arrow whose `loop` delays the fed back value.
  */
@compileTimeOnly("rec was not removed by macro")
def rec[F[_, _], A](body: RecScope[F] ?=> A)(using ArrowLoop[F]): ArrowSyntax[F, A] =
  sys.error("rec was not removed by macro")

object arrows:
  inline def lift[F[_, _]](using arrow: Arrow[F])[A, B](f: A => B): F[A, B] = arrow.lift(f)

  inline def id[F[_, _]](using arrow: Arrow[F])[A]: F[A, A] = arrow.id

  inline def proc[A](using DummyImplicit)[F[_, _] : {Arrow as arrow}, B](inline syntax: A => ArrowSyntax[F, B]): F[A, B] =
    ${ procImpl[F, A, B]('{ syntax }, '{ arrow }) }
