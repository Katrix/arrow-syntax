package arrowSyntax

import cats.arrow.Arrow

trait ArrowLoop[F[_, _]] extends Arrow[F]:
  extension [A, B, C](f: F[(A, C), (B, C)])
    def loop: F[A, B]