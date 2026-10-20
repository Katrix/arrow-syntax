package arrowSyntax

import arrowSyntax.inlineSyntax.*
import cats.Monad
import cats.arrow.{Arrow, ArrowChoice}
import cats.data.Kleisli

trait ArrowApply[F[_, _]] extends ArrowChoice[F]:
  def app[A, B]: F[(F[A, B], A), B]

  extension [A, B](arr: F[A, B])
    def rmapWith[C, D](f: B => (F[C, D], C)): F[A, D] =
      given Arrow[F] = this
      arr.rmap(f).andThen(app)

object ArrowApply:
  given ArrowApply[Function1]:
    def lift[A, B](f: A => B): A => B                             = f
    def compose[A, B, C](f: B => C, g: A => B): A => C            = g.andThen(f)
    def first[A, B, C](fa: A => B): ((A, C)) => (B, C)           = (a, c) => (fa(a), c)
    def choose[A, B, C, D](f: A => C)(g: B => D): Either[A, B] => Either[C, D] =
      _.fold(a => Left(f(a)), b => Right(g(b)))
    def app[A, B]: ((A => B, A)) => B = (f, a) => f(a)

  given kleisliArrowApply: [M[_]] => (M: Monad[M]) => ArrowApply[[A, B] =>> Kleisli[M, A, B]]:
    def lift[A, B](f: A => B): Kleisli[M, A, B]                                         = Kleisli(a => M.pure(f(a)))
    def compose[A, B, C](f: Kleisli[M, B, C], g: Kleisli[M, A, B]): Kleisli[M, A, C] = g.andThen(f)
    def first[A, B, C](fa: Kleisli[M, A, B]): Kleisli[M, (A, C), (B, C)]                = fa.first[C]
    def choose[A, B, C, D](f: Kleisli[M, A, C])(g: Kleisli[M, B, D]): Kleisli[M, Either[A, B], Either[C, D]] =
      Kleisli(_.fold(a => M.map(f.run(a))(Left(_)), b => M.map(g.run(b))(Right(_))))
    def app[A, B]: Kleisli[M, (Kleisli[M, A, B], A), B] = Kleisli((k, a) => k.run(a))
