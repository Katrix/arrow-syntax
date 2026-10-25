package arrowSyntax

import cats.arrow.ArrowChoice
import arrowSyntax.inlineSyntax.*

trait MyArrow[A, B]
object MyArrow:
  given ArrowChoice[MyArrow] = ???

def arrow[A, B]: MyArrow[A, B] = ???

val test1 = arrows.proc[Int]: a =>
  println("Test")
  val arr1 = arrow[Int, Long]
  val arr2 = arrow[Int, Boolean]
  val arr3 = arrow[Long, String]
  val arr4 = arrow[Int, String]
  val arr5 = arrow[Long, String]
  val arr6 = arrow[Int, (Long, Long)]

  for
    (i1, i2) <- arr6 -< a
    l        <- arr1 -< a
    b        <- arr2 -< a
    r1       <- if b then arr3 -< l else arr4 -< a
    r2       <- b match
      case true  => arr3 -< l
      case false => arr4 -< a
//    r3 <- (if b then arr3 else arr5) -<< l //cant pipe b in
    r3 <- (if true then arr3 else arr5) -< l // this works
  yield (r1, r2, r3)

/*
val result1Step1 = arrows.proc[Int]: a =>
  val arr1 = arrow[Int, Long]
  val arr2 = arrow[Int, Boolean]
  val arr3 = arrow[Long, String]
  val arr4 = arrow[Int, String]
  val arr5 = arrow[Long, String]

  (arr1 -< a)
    .flatMap(l =>
      (arr2 -< a)
        .flatMap(b =>
          (if b then arr3 -< l else arr4 -< a)
            .flatMap(r1 =>
              {
                b match
                  case true  => arr3 -< l
                  case false => arr4 -< a
              }
                .flatMap(r2 =>
                  ((if b then arr3 else arr5) -< l)
                    .map(r3 => (r1, r2))
                )
            )
        )
    )
 */

val result1Step2 =
  val arr1 = arrow[Int, Long]
  val arr2 = arrow[Int, Boolean]
  val arr3 = arrow[Long, String]
  val arr4 = arrow[Int, String]
  val arr5 = arrow[Long, String]

  val ev = summon[ArrowChoice[MyArrow]]

  ev.lift((a: Int) => (a, a))
    .andThen(arr1.first)
    .rmap((l, a) => (a, (a, l)))
    .andThen(arr2.first)
    .rmap { case (b, (a, l)) => (if b then Left(l) else Right(a), (a, l, b)) }
    .andThen(ev.choice(arr3, arr4).first)
    .rmap { case (r1, (a, l, b)) => (if b then Left(l) else Right(a), (a, l, b, r1)) }
    .andThen(ev.choice(arr3, arr4).first)
    .rmap { case (r2, (a, l, b, r1)) => (if b then Left(l) else Right(l), (a, l, b, r1, r2)) }
    .andThen(ev.choice(arr3, arr5).first)
    .rmap { case (r3, (a, l, b, r1, r2)) => (r1, r2) }

val result1Step3 =
  val arr1 = arrow[Int, Long]
  val arr2 = arrow[Int, Boolean]
  val arr3 = arrow[Long, String]
  val arr4 = arrow[Int, String]
  val arr5 = arrow[Long, String]

  val ev = summon[ArrowChoice[MyArrow]]

  ev.lift((a: Int) => (a, a))
    .andThen(arr1.first)
    .rmap((l, s) => (s, (s, l)))
    .andThen(arr2.first)
    .rmap { case (b, (a, l)) => (if b then Left(l) else Right(a), (a, l, b)) }
    .andThen(ev.choice(arr3, arr4).first)
    .rmap { case (r1, (a, l, b)) => (if b then Left(l) else Right(a), (l, b, r1)) }
    .andThen(ev.choice(arr3, arr4).first)
    .rmap { case (r2, (l, b, r1)) => (if b then Left(l) else Right(l), (r1, r2)) }
    .andThen(ev.choice(arr3, arr5).first)
    .rmap { case (r3, (r1, r2)) => (r1, r2) }
