package arrowSyntax.inlineSyntax

import cats.arrow.{Arrow, ArrowChoice}

extension [F[_, _]: {Arrow as arrow}, A, B](arr: F[A, B])
  inline def andThen[C](arr2: F[B, C]): F[A, C] = arrow.compose(arr2, arr)

  inline def rmap[C](f: B => C): F[A, C] = arr.andThen(arrow.lift(f))

  inline def split[C, D](arr2: F[C, D]): F[(A, C), (B, D)] = arrow.split(arr, arr2)

  inline def merge[C](arr2: F[A, C]): F[A, (B, C)] = arrow.merge(arr, arr2)

  inline def first[C]: F[(A, C), (B, C)] = arrow.first(arr)

  inline def second[C]: F[(C, A), (C, B)] = arrow.second(arr)

  inline def leftNarrow[AA <: A]: F[AA, B] = arr.asInstanceOf[F[AA, B]]

  inline def rightWiden[BB >: B]: F[A, BB] = arr.asInstanceOf[F[A, BB]]

extension [F[_, _]: {ArrowChoice as arrow}, A, B](arr: F[A, B])
  def choice[C](arr2: F[C, B]): F[Either[A, C], B] = arrow.choice(arr, arr2)
