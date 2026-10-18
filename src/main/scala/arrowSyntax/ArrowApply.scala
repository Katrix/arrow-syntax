package arrowSyntax

import arrowSyntax.inlineSyntax.*
import cats.arrow.{Arrow, ArrowChoice}

trait ArrowApply[F[_, _]] extends ArrowChoice[F]:
  def app[A, B]: F[(F[A, B], A), B]

  extension [A, B](arr: F[A, B])
    def rmapWith[C, D](f: B => (F[C, D], C)): F[A, D] =
      given Arrow[F] = this
      arr.rmap(f).andThen(app)
