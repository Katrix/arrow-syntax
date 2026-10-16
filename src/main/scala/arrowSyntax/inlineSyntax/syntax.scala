package arrowSyntax.inlineSyntax

import cats.arrow.Arrow

extension [F[_, _]: {Arrow as arrow}, A, B](arr: F[A, B])
  inline def andThen[C](arr2: F[B, C]): F[A, C] = arrow.compose(arr2, arr)
  
  inline def rmap[C](f: B => C): F[A, C] = arr.andThen(arrow.lift(f))
  
  inline def first[C]: F[(A, C), (B, C)] = arrow.first(arr)

  inline def leftNarrow[AA <: A]: F[AA, B] = arr.asInstanceOf[F[AA, B]]

  inline def rightWiden[BB >: B]: F[A, BB] = arr.asInstanceOf[F[A, BB]]