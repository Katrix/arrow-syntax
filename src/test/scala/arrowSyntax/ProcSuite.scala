package arrowSyntax

import scala.compiletime.testing.typeCheckErrors

import cats.arrow.Arrow
import cats.data.{Kleisli, Writer}
import weaver.FunSuite

object ProcSuite extends FunSuite:

  // An arrow with only an Arrow instance, no ArrowChoice
  final case class Plain[A, B](run: A => B)
  object Plain:
    given Arrow[Plain]:
      def lift[A, B](f: A => B): Plain[A, B]                            = Plain(f)
      def compose[A, B, C](f: Plain[B, C], g: Plain[A, B]): Plain[A, C] = Plain(g.run.andThen(f.run))
      def first[A, B, C](fa: Plain[A, B]): Plain[(A, C), (B, C)]        = Plain((a, c) => (fa.run(a), c))

  // An arrow which records every invocation, to check ordering and that only the taken branch runs
  type Log[X]       = Writer[List[String], X]
  type Logged[A, B] = Kleisli[Log, A, B]
  def logged[A, B](name: String)(f: A => B): Logged[A, B] = Kleisli(a => Writer(List(name), f(a)))

  val inc: Int => Int           = _ + 1
  val double: Int => Int        = _ * 2
  val isEven: Int => Boolean    = _ % 2 == 0
  val show: Int => String       = _.toString
  val length: String => Int     = _.length
  val divMod: Int => (Int, Int) = a => (a / 10, a % 10)

  test("single arrow application"):
    val f = arrows.proc[Int]: a =>
      for b <- double -< a yield b

    expect.eql(10, f(5))

  test("yield can transform the result"):
    val f = arrows.proc[Int]: a =>
      for b <- double -< a yield s"result: $b"

    expect.eql("result: 10", f(5))

  test("later steps can use earlier binders and the input"):
    val f = arrows.proc[Int]: a =>
      for
        b <- inc -< a
        c <- double -< b
        d <- show -< (a + c)
      yield (a, b, c, d)

    expect.eql((3, 4, 8, "11"), f(3))

  test("unused binders are dropped without affecting the result"):
    val f = arrows.proc[Int]: a =>
      for
        b <- inc -< a
        c <- double -< a
        _ <- show -< c
        d <- inc -< b
      yield d

    expect.eql(7, f(5))

  test("tuple patterns in generators"):
    val f = arrows.proc[Int]: a =>
      for
        (tens, ones) <- divMod -< a
        t            <- double -< tens
      yield (t, ones)

    expect.eql((8, 2), f(42))

  test("untupled lambda parameters"):
    val repeat: ((String, Int)) => String = (s, n) => s * n

    val f = arrows.proc[(String, Int)]: (s, n) =>
      for
        r <- repeat -< (s, n)
        l <- length -< r
      yield (r, l)

    expect.eql(("abab", 4), f(("ab", 2)))

  test("pattern matching lambda parameters"):
    val f = arrows.proc[(Int, Int)] { case (x, y) =>
      for
        a <- double -< x
        b <- inc -< y
      yield a + b
    }

    expect.eql(10, f((3, 3)))

  test("preamble statements are kept"):
    val f = arrows.proc[Int]: a =>
      val triple: Int => Int = _ * 3
      val offset             = 100

      for b <- triple -< (a + offset) yield b

    expect.eql(306, f(2))

  test("if/else uses ArrowChoice"):
    val f = arrows.proc[Int]: a =>
      for
        even <- isEven -< a
        r    <- if even then show -< a else show -< (a * 100)
      yield r

    expect.eql("4", f(4)) && expect.eql("500", f(5))

  test("if/else branches can feed different input types"):
    val f = arrows.proc[Int]: a =>
      for
        s    <- show -< a
        even <- isEven -< a
        r    <- if even then length -< s else double -< a
      yield r

    expect.eql(4, f(1234)) && expect.eql(14, f(7))

  test("match uses ArrowChoice"):
    val f = arrows.proc[Int]: a =>
      for r <- a match
          case 0          => show -< a
          case 1          => show -< (a * 10)
          case n if n < 0 => show -< -n
          case n          => show -< (n + 1)
      yield r

    expect.eql("0", f(0)) &&
    expect.eql("10", f(1)) &&
    expect.eql("5", f(-5)) &&
    expect.eql("8", f(7))

  test("match case binders can be used as arrow inputs"):
    val f = arrows.proc[Option[(Int, String)]]: o =>
      for
        r <- o match
          case Some((n, s)) => length -< (s * n)
          case None         => inc -< -1
        d <- double -< r
      yield d

    expect.eql(12, f(Some((3, "ab")))) && expect.eql(0, f(None))

  test("match on an earlier binder"):
    val f = arrows.proc[Int]: a =>
      for
        (tens, ones) <- divMod -< a
        r            <- tens match
          case 0 => show -< ones
          case t => show -< (t * ones)
      yield r

    expect.eql("7", f(7)) && expect.eql("8", f(42))

  test("more than 22 live binders"):
    val f = arrows.proc[Int]: a =>
      for
        x1  <- inc -< a
        x2  <- inc -< x1
        x3  <- inc -< x2
        x4  <- inc -< x3
        x5  <- inc -< x4
        x6  <- inc -< x5
        x7  <- inc -< x6
        x8  <- inc -< x7
        x9  <- inc -< x8
        x10 <- inc -< x9
        x11 <- inc -< x10
        x12 <- inc -< x11
        x13 <- inc -< x12
        x14 <- inc -< x13
        x15 <- inc -< x14
        x16 <- inc -< x15
        x17 <- inc -< x16
        x18 <- inc -< x17
        x19 <- inc -< x18
        x20 <- inc -< x19
        x21 <- inc -< x20
        x22 <- inc -< x21
        x23 <- inc -< x22
        x24 <- inc -< x23
      yield List(
        a,
        x1,
        x2,
        x3,
        x4,
        x5,
        x6,
        x7,
        x8,
        x9,
        x10,
        x11,
        x12,
        x13,
        x14,
        x15,
        x16,
        x17,
        x18,
        x19,
        x20,
        x21,
        x22,
        x23,
        x24
      )

    expect.eql((0 to 24).toList, f(0))

  test("works with arrows that only have an Arrow instance"):
    val plainInc    = Plain(inc)
    val plainDouble = Plain(double)

    val f = arrows.proc[Int]: a =>
      for
        b <- plainInc -< a
        c <- plainDouble -< b
      yield (a, b, c)

    expect.eql((2, 3, 6), f.run(2))

  test("arrows run once each, in order"):
    val first  = logged[Int, Int]("first")(inc)
    val second = logged[Int, Int]("second")(double)
    val third  = logged[Int, String]("third")(show)

    val f = arrows.proc[Int]: a =>
      for
        b <- first -< a
        c <- second -< b
        d <- third -< (a + c)
      yield d

    val (log, res) = f.run(1).run
    expect.eql(List("first", "second", "third"), log) && expect.eql("5", res)

  test("only the taken branch runs"):
    val check = logged[Int, Boolean]("check")(isEven)
    val left  = logged[Int, String]("left")(show)
    val right = logged[Int, String]("right")(show)

    val f = arrows.proc[Int]: a =>
      for
        even <- check -< a
        r    <- if even then left -< a else right -< a
      yield r

    expect.eql(List("check", "left"), f.run(2).run._1) &&
    expect.eql(List("check", "right"), f.run(3).run._1)

  test("only the matched case runs"):
    val zero = logged[Int, String]("zero")(show)
    val neg  = logged[Int, String]("neg")(show)
    val pos  = logged[Int, String]("pos")(show)

    val f = arrows.proc[Int]: a =>
      for r <- a match
          case 0          => zero -< a
          case n if n < 0 => neg -< n
          case n          => pos -< n
      yield r

    expect.eql(List("zero"), f.run(0).run._1) &&
    expect.eql(List("neg"), f.run(-1).run._1) &&
    expect.eql(List("pos"), f.run(1).run._1)

  test("if/else without ArrowChoice is a compile error"):
    val errors = typeCheckErrors("""
      val plainShow = Plain(show)
      arrows.proc[Int]: a =>
        for r <- if a > 0 then plainShow -< a else plainShow -< -a
        yield r
    """)

    expect(errors.exists(_.message.contains("ArrowChoice")))

  test("arrows can use preamble definitions"):
    val f = arrows.proc[Int]: a =>
      val offset                = 100
      val addOffset: Int => Int = _ + offset

      for b <- addOffset -< a yield b

    expect.eql(105, f(5))

  test("an arrow using an earlier binder is a compile error"):
    val errors = typeCheckErrors("""
      arrows.proc[Int]: a =>
        for
          b <- inc -< a
          c <- ((x: Int) => x + b) -< a
        yield c
    """)

    expect(errors.exists(_.message.contains("cannot depend on `b`")))

  test("an arrow using the proc input is a compile error"):
    val errors = typeCheckErrors("""
      arrows.proc[Int]: a =>
        for b <- ((x: Int) => x + a) -< a yield b
    """)

    expect(errors.exists(_.message.contains("cannot depend on `a`")))

  test("an arrow using an untupled proc input is a compile error"):
    val errors = typeCheckErrors("""
      arrows.proc[(Int, Int)]: (x, y) =>
        for b <- ((z: Int) => z + y) -< x yield b
    """)

    expect(errors.exists(_.message.contains("cannot depend on `y`")))

  test("an arrow using a match case binder is a compile error"):
    val errors = typeCheckErrors("""
      arrows.proc[Option[Int]]: o =>
        for
          r <- o match
            case Some(n) => ((x: Int) => x + n) -< n
            case None    => inc -< 0
        yield r
    """)

    expect(errors.exists(_.message.contains("cannot depend on `n`")))

  test("a preamble using the proc input is a compile error"):
    val errors = typeCheckErrors("""
      arrows.proc[Int]: a =>
        val offset = a + 1
        for b <- inc -< offset yield b
    """)

    expect(errors.exists(_.message.contains("cannot depend on the proc input `a`")))

  test("a body that is a single command is the same as a for comprehension yielding it"):
    val f = arrows.proc[Int]: a =>
      double -< a

    expect.eql(10, f(5))

  test("an ArrowSyntax value constructed elsewhere is a compile error"):
    val errors = typeCheckErrors("""
      val s: ArrowSyntax[Function1, Int] = null
      arrows.proc[Int]: a =>
        for
          b <- double -< a
          c <- s
        yield c
    """)

    expect(errors.exists(_.message.contains("Expected -< or -<<")))

  test("a bare ArrowSyntax value constructed elsewhere is a compile error"):
    val errors = typeCheckErrors("""
      val s: ArrowSyntax[Function1, Int] = null
      arrows.proc[Int]: a =>
        s
    """)

    expect(errors.exists(_.message.contains("Expected -< or -<<")))

  test("a body of type Nothing is a compile error, not a macro crash"):
    val errors = typeCheckErrors("""
      arrows.proc[Int](using DummyImplicit.dummyImplicit)[Function1, Int]: a =>
        ???
    """)

    expect(errors.exists(_.message.contains("Expected -< or -<<"))) &&
    expect(errors.forall(!_.message.contains("Exception occurred")))

  test("-<< can apply an arrow that depends on earlier binders"):
    val f = arrows.proc[Int]: a =>
      for
        b <- inc -< a
        c <- ((x: Int) => x * b) -<< a
      yield (b, c)

    expect.eql((4, 12), f(3))

  test("-<< can apply an arrow that depends on the proc input"):
    val f = arrows.proc[Int]: a =>
      ((x: Int) => x + a) -<< (a * 10)

    expect.eql(33, f(3))

  test("-<< arrows run in order with the other arrows"):
    val first  = logged[Int, Int]("first")(inc)
    val second = (n: Int) => logged[Int, String](s"second $n")(show)

    val f = arrows.proc[Int]: a =>
      for
        b <- first -< a
        c <- second(b) -<< a
      yield c

    val (log, res) = f.run(1).run
    expect.eql(List("first", "second 2"), log) && expect.eql("1", res)

  test("-<< inside if/else and match"):
    val f = arrows.proc[Int]: a =>
      for
        even <- isEven -< a
        r    <- if even then ((x: Int) => x + a) -<< a else double -< a
        s    <- r match
          case 0 => show -< r
          case n => ((x: Int) => s"$n:$x") -<< r
      yield s

    expect.eql("8:8", f(4)) && expect.eql("0", f(0)) && expect.eql("10:10", f(5))

  test("-<< without ArrowApply is a compile error"):
    val errors = typeCheckErrors("""
      val plainShow = Plain(show)
      arrows.proc[Int]: a =>
        plainShow -<< a
    """)

    expect(errors.exists(_.message.contains("ArrowApply")))

  test("if/else branch inputs can contain lambdas"):
    val f = arrows.proc[Int]: a =>
      for r <- if a > 0 then double -< List(a).map(x => x + 1).head else double -< a
      yield r

    expect.eql(8, f(3)) && expect.eql(-6, f(-3))
