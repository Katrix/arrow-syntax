# arrow-syntax

In Haskell, arrow notation is a way to write programs using arrows in an easier way. arrow-notation ports that functionality to Scala.

```scala
libraryDependencies += "net.katsstuff" %% "arrow-syntax" % "0.1.0"
```

## Usage

Arrow notation reuses Scala's for comprehension inside a magic macro called
`arrows.proc[A]`. `A` here is the input type to the resulting arrow. The body
of `arrows.proc` should be a for comprehension (though you're allowed to
place values and such before it) made up of commands, where a command takes the
form `arrowOutput <- arrow -< arrowInput`.

The output of the arrow is the normal output in a for comprehension, so you can
do with it roughly what you can in normal for comprehension.

`if` and `match` work to some degree within arrow notation, so you can do
branching as well.

Here's an example:
```scala
val test1 = arrows.proc[Int]: a =>
  println("Code inside proc")

  for
    (i1, i2) <- tupleArr -< a
    l        <- toLongArr -< a
    b        <- toBoolArr -< a
    r1       <- if b then arr3 -< l else arr4 -< a
    r2       <- b match
      case true  => arr3 -< l
      case false => arr4 -< a
  yield (r1, r2)
```

Typically the macro will check that the arrows don't depend on values that
they shouldn't have access to. For example, here are two compile errors:
```scala
val error = arrows.proc[Int]: a =>
  // Not allowed, a is technically not defined here, use an arrow returning Unit instead
  println(s"Got $a")
  
  for
    r <- makeArrow(a) -< // Also not allowed
  yield r
```

If we look at what this would compile to, the errors might make more sense:
```scala
val error = 
  println(s"Got $a")
  
  arrows.lift(a => a).andThen(makeArrow(a))
```

If you truly do want to construct an arrow from an arrow value, and then use
that arrow, and your arrow has an instance of `ArrowApply` (see down below),
you can use `-<<` to pass the value instead.

For example:
```scala
val fine = arrows.proc[Int]: a =>
  for
    r <- makeArrow(a) -<< a
  yield r
```

## Extra utilities

In addition to the arrow notation itself, arrow-syntax also brings a few extra utilities for writing code using arrows.

```scala
import arrowSyntax.*

def useArr(arr: MyArrow[Int, Int]) = arr

// Create an identity arrow. Type is inferred
useArr(arrows.id[MyArrow])

// The type of the arrow can also be set explicitly
useArr(arrows.id[MyArrow][Int])

// There is also a utility to lift a function. The arrow is inferred
useArr(arrows.lift((i: Int) => i + 2))

// The type can yet again be passed explicitly
useArr(arrows.lift[MyArrow]((i: Int) => i + 2))
```

## More typeclasses

arrow-notation brings two new typeclasses to support part of it's notation.


### ArrowApply

ArrowApply is your Monad equivalent. Normally, arrows have to be defined at the
top level. If you have an arrow `a`, you cannot create an arrow `b` from the
result of `a` and run it without using ArrowApply.

Definition:
```scala
trait ArrowApply[F[_, _]] extends ArrowChoice[F]:
  def app[A, B]: F[(F[A, B], A), B]

  extension [A, B](arr: F[A, B])
    def rmapWith[C, D](f: B => (F[C, D], C)): F[A, D] =
      given Arrow[F] = this
      arr.rmap(f).andThen(app)
```

Think of `app` as your `flatten` analog, and `rmapWith` as your `flatMap` analog.


### ArrowLoop

ArrowLoop allows you to construct recursive arrows.

```scala
trait ArrowLoop[F[_, _]] extends Arrow[F]:
  extension [A, B, C](f: F[(A, Eval[C]), (B, C)]) def loop: F[A, B]
```

Think of `loop` kind of like a `fix`.