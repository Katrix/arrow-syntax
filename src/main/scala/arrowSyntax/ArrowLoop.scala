package arrowSyntax

import cats.Eval
import cats.arrow.Arrow

trait ArrowLoop[F[_, _]] extends Arrow[F]:
  /**
    * Feeds the second output of `f` back in as its second input. The fed back
    * value is not known until `f` has produced it, so it is passed as an
    * [[Eval]] which must not be forced before then.
    */
  extension [A, B, C](f: F[(A, Eval[C]), (B, C)]) def loop: F[A, B]

object ArrowLoop:
  given ArrowLoop[Function1]:
    def lift[A, B](f: A => B): A => B                   = f
    def compose[A, B, C](f: B => C, g: A => B): A => C  = g.andThen(f)
    def first[A, B, C](fa: A => B): ((A, C)) => (B, C) = (a, c) => (fa(a), c)

    extension [A, B, C](f: ((A, Eval[C])) => (B, C))
      def loop: A => B = a =>
        lazy val res: (B, C) = f((a, Eval.later(res._2)))
        res._1
