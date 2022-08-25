# Applicative Functors

Building on [Functors](functors.md) is the [Applicative Functor](https://en.wikipedia.org/wiki/Applicative_functor). For simplicity, you can refer to these simply as "Applicatives". These are a little tricker than functors, but still simpler than monads. Let's they work!

# What is an Applicative Functor?

An applicative functor is an defines a default or "base" construction for an object and allows
function application to be chained across multiple instances of the structure. All applicative
functors are functors, meaning they must also support the "map" operation.

# How are Applicatives represented in Lean?

An [applicative functor](https://en.wikipedia.org/wiki/Applicative_functor) is an intermediate
structure between `Functor` and `Monad`. It mainly consists of two operations:

* `pure : α → F α`
* `seq : F (α → β) → F α → F β` (written as `<*>`)

The `pure` operator tells us how we can wrap a normal object into an instance of this structure.
This is the "default" mechanism mentioned above.

The `seq` operator gives a notion of evaluation order to the effects, where
the first argument is executed before the second, but unlike a monad the results
of earlier computations cannot be used to define later actions.

Applicative in Lean is built on some helper type classes, `Functor`, `Pure` and `Seq`:

```lean
# namespace hidden
class Applicative (f : Type u → Type v) extends Functor f, Pure f, Seq f, SeqLeft f, SeqRight f where
  map      := fun x y => Seq.seq (pure x) fun _ => y
  seqLeft  := fun a b => Seq.seq (Functor.map (Function.const _) a) b
  seqRight := fun a b => Seq.seq (Functor.map (Function.const _ id) a) b
# end hidden
```

Notice that as with `Functor` it is also a type transformer `(f : Type u → Type v)` and notice
the `extends Functor f` is ensuring the base Functor also performs that same transformation.

As stated above, all applicatives are then functors. This means we can assume that `map` already
exists for all these types.

The `Pure` base type class is a very simple type class that supplies the `pure` function.

```lean
# namespace hidden
class Pure (f : Type u → Type v) where
  pure {α : Type u} : α → f α
# end hidden
```

You can think of it as lifing the result of a pure value to some monadic type.
The simplest example of `pure` is the `Option` type:

```lean
#eval (pure 10 : Option Nat)  -- some 10
```

Here we used the `Option` implementation of `pure` to wrap the `Nat 10` value in an `Option Nat`
type resulting in the value `some 10`, and in fact if you look at the Monad instance of Option, you
will see that `pure` is indeed implemented using `Option.some`:

```lean
# namespace hidden
instance : Monad Option where
    pure := Option.some
# end hidden
```

The `Seq` type class is also a simple type class that provides the `seq` operator which can
also be written using the special syntax `<*>`.

```lean
# namespace hidden
class Seq (f : Type u → Type v) : Type (max (u+1) v) where
  seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β
# end hidden
```

The `seq` operator allows you to chain operations by wrapping a function in a structure. The name
"applicative" comes from the fact that you "apply" functions from within the structure, rather than
simply from outside the structure, as was the case with `Functor.map`.

## Basic Applicative Examples

Many of our basic functors also have instances of `Applicative` inherited from their Monad instances.
For example, `Option` is a Monad which means it is also `Applicative`.

So let's take a look and what the `seq` operator can do.  Suppose you want to multiply two `Option Nat`
objects.  Your first attempt might be this:

```lean
#check_failure (some 4) * (some 5)      -- failed to synthesize instance
```

You then might wonder how to use the `Functor.map` to solve this since we could do these before:

```lean
#eval (some 4).map (fun x => x * 5)  -- some 20

#eval (some 4).map (· * 5)  -- some 20

#eval (· * 5) <$> (some 4)   -- some 20
```

Remember that `<$>` is the infix notation for `Functor.map`.  Lean is very powerful and lets you
define your own syntax, so `<$>` is nothing special.  You could define your own infix operator like this:

```lean
@[inheritDoc] infixr:100 " doodle " => Functor.map

#eval (· * 5) doodle (some 4)   -- some 20
```

The functor map operation can apply a multiplication to the value in the Option and then lift the
result back up to become a new Option, but this isn't what we need here.

The `Seq.seq` operator `<*>` can help since it can apply a function to the items inside our
container and then lift the result back up to our desired type, namely Option.

There are two ways to do this:

```lean
#eval pure (.*.) <*> some 4 <*> some 5 -- some 20

#eval (.*.) <$> some 4 <*> some 5 -- some 20
```

In the first way, we start off by wrapping our function in an applicative using pure. Then we apply
this to the first Option, and again to the second Option in a chain of operations.  So  you can see
how `Seq.seq` can be chained in fact, `Seq.seq` is really all about chaining of operations.

But in this case there is a simpler way.  In the second way, we observe that "applying" a single
function to a container is the same as using `Functor.map`. So we use `<$>` to "transform" the first
option into an Option containing a function, and then apply this function over our second value.

Now if either side is `none`, our result is `none`, as expected, and in this case the
`seq` operator was able to eliminate the multiplication:

```lean
#eval (.*.) <$> none <*> some 5  -- none
#eval (.*.) <$> some 4 <*> none  -- none
```

For a more interesting example, let's make `List` an Applicative by adding the following
definition:

```lean
instance : Applicative List where
  pure := List.pure
  seq f x := List.bind f fun y => Functor.map y (x ())
```

Notice we can now sequence a _list_ of functions and a _list_ of items.
The trivial case of sequencing a singleton list is in fact the same as map as we saw
earlier with the Option examples:

```lean
# ++
#eval [(·+2)] <*> [4, 6] -- [6, 8]
#eval (·+2) <$> [4,6]    -- [6, 8]
```

But now with list it is easier to show the difference when you do this:

```lean
# ++
#eval [(· +2), (· *3)] <*> [4, 6] -- [6, 8, 12, 18]
```

Why did this produce 4 values?  The reason is because `<*>` applies _every_ function to _every_
value in a pairwise manner.  This makes sequence really convenient for solving certain problems. For
example, how do we get the pairwise combinations of all values from two lists?

```lean
# ++
#eval Prod.mk <$> [1, 2, 3] <*> [4, 5, 6]
-- [(1, 4), (1, 5), (1, 6), (2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6)]
```

How do you get the sum of these pairwise values?
```lean
# ++
#eval (·+·) <$> [1, 2, 3] <*> [4, 5, 6]
-- [5, 6, 7, 6, 7, 8, 7, 8, 9]
```

Here we use `<$>` to "transform" each element of the first list into a function, and then apply
these functions over our second list.

If you have 3 lists, and want to find all combinations of 3 values across those lists you
would need helper function that can create a tuple out of 3 values, and Lean provides a
very convenient syntax for that `(·,·,·)`:

```lean
# ++
#eval (·,·,·) <$> [1, 2] <*> [3, 4] <*> [5, 6]
-- [(1, 3, 5), (1, 3, 6), (1, 4, 5), (1, 4, 6), (2, 3, 5), (2, 3, 6), (2, 4, 5), (2, 4, 6)]
```

And you could sum these combinations if you first define a sum function that takes three inputs and
then you could chain apply this over the three lists.  Again lean can create such a function
with the expression `(·+·+·)`:

```lean
# ++
#eval (·+·+·) <$> [1, 2] <*> [3, 4] <*> [5, 6]
-- [9, 10, 10, 11, 10, 11, 11, 12]
```

And indeed each sum here matches the expected values if you manually sum the triples we
show above.

**Side note:** there is another way to combine lists with a function that does not do the pairwise
combinatorics, it is called `List.zipWith`:

```lean
#eval List.zipWith (·+·) [1, 2, 3] [4, 5, 6]
-- [5, 7, 9]
```

And there is a helper function named `List.zip` that calls `zipWith` using the function `Prod.mk`
so you get a nice zipped list like this:

```lean
#eval List.zip [1, 2, 3] [4, 5, 6]
-- [(1, 4), (2, 5), (3, 6)]
```

And of couse, as you would expect, there is an `unzip` also:

```lean
#eval List.unzip (List.zip [1, 2, 3] [4, 5, 6])
-- ([1, 2, 3], [4, 5, 6])
```

## Example: A Functor that is not Applicative

From the chapter on [functors](functors.md) you might remember this example of `LivingSpace`
that had a `Functor` instance:

```lean
structure LivingSpace (α: Type) where
  totalSize : α
  numBedrooms : Nat
  masterBedroomSize : α
  livingRoomSize : α
  kitchenSize : α
  deriving Repr, BEq

def LivingSpace.map (f : α → β) (s : LivingSpace α) : LivingSpace β :=
  { totalSize := f s.totalSize,
    numBedrooms := s.numBedrooms,
    masterBedroomSize := f s.masterBedroomSize,
    livingRoomSize := f s.livingRoomSize,
    kitchenSize := f s.kitchenSize }

instance : Functor LivingSpace where
  map := LivingSpace.map
```

It wouldn't really make sense to make an `Applicative` instance here. How would you write `pure` in
the `Applicative` instance? By taking a single value and plugging it in for total size _and_ the
master bedroom size _and_ the living room size? That wouldn't really make sense. And what would the
numBedrooms value be for the default? What would it mean to "chain" two of these objects together?

If you can't answer these questions very well, then it suggests this type isn't really an
Applicative functor.

## What are the Applicative Laws?

While functors had two laws, applicatives have four laws which we can test using our
applicative list:

### Identity

`pure id <*> v = v`

Applying the identity function through an applicative structure should not change the underlying
values or structure:

For example:
```lean
# instance : Applicative List where
#   pure := List.pure
#   seq f x := List.bind f fun y => Functor.map y (x ())
#eval pure id <*> [1, 2, 3]  -- [1, 2, 3]
```

We can prove this for all values `v` with this theorem:

```lean
# ++
example [Applicative m] [LawfulApplicative m] (v : m α) :
  pure id <*> v = v :=
  by simp -- Goals accomplished 🎉
```

### Homomorphism

`pure f <*> pure x = pure (f x)`

For example:

```lean
# ++
#eval let x := 1
      let f := (· + 2)
      pure f <*> pure x = (pure (f x) : List Nat) -- true
```

### Interchange

`u <*> pure y = pure (. y) <*> u`.

For example:

```lean
# ++
#eval let y := 4
      let u : List (Nat → Nat) := [(· + 2)]
      u <*> pure y = pure (· y) <*> u      -- true
```

Note that (· y) is short hand for: `fun f => f y`.

### Composition:

`pure (.) <*> u <*> v <*> w = u <*> (v <*> w)`

```lean
# ++
#eval pure (·+·+·) <*> [1, 2] <*> [3, 4] <*> [5, 6] -- [9, 10, 10, 11, 10, 11, 11, 12]

#eval let grouped := pure (·+·) <*> [3, 4] <*> [5, 6]
      pure (·+·) <*> [1, 2] <*> grouped -- [9, 10, 10, 11, 10, 11, 11, 12]
```

With composition we implemented the grouping `(v <*> w)` then showed you could
use that in the outer sequence to get the same final result `[9, 10, 10, 11, 10, 11, 11, 12]`.

Ultimately though, these laws encapsulate the same ideas as the functor laws which can be summarized
in the following three statements:

1. Applying pure should not change the underlying values or functions
1. Applying the identity function through an applicative structure should not change the underlying
   values or structure.
1. It should not matter what order we group operations in. This third idea in particular is useful
because it means that we can apply parallelism to a long chain of applicative operations. This also
comes down to the fact that applicative functors are context-free, an idea we'll discuss more with
monads.

## How do Applicatives help with Monads?

Applicatives are helpful for the same reasons as functors. They're a relatively simple abstract
structure that has practical applications in our code. Now that we understand how chaining
operations can fit into a structure definition, we're in a good position to start thinking about
monads!

## Lazy Evaluation

If you write our simple Option example `(.*.) <$> some 4 <*> some 5` that produces `some 20`
using `Seq.seq` you will see somthing interesting:

```lean
#eval Seq.seq ((.*.) <$> (some 4)) (fun (_ : Unit) => (some 5)) -- some 20
```

This may look a bit combersome, specifically, why did we need to invent this
function `(fun (_ : Unit) => (some 5)`?

Well if you take a close look at the type class definition:
```lean
# namespace hidden
class Seq (f : Type u → Type v) : Type (max (u+1) v) where
  seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β
# end hidden
```

You will see this function defined here: `(Unit → f α)`, this is a function that takes `Unit` as input
and produces the output of type `f α` where `f` is our container type `Type u`, in our example `Option`
and `α` is our element type `Nat`, so `(fun (_ : Unit) => (some 5)` matches this definition because
it is taking an input of type Unit and producing `some 5` which is type `Option Nat`.

The reason is `seq` is defined this way is because Lean is an eagerly evaluated language
(call-by-value), you have to use this kind of Unit function whenever you want to explicitly delay
evaluation and `seq` wants that so it can eliminate unnecessary function evaluations whenever
possible.  This happened, in fact, with our example using `none` values
`#eval (.*.) <$> none <*> some 5  -- none`.

Now to complete this picture you will find the default implementation of `seq` on the Lean `Monad`
type class:

```lean
# namespace hidden
class Monad (m : Type u → Type v) extends Applicative m, Bind m : Type (max (u+1) v) where
  map      f x := bind x (Function.comp pure f)
  seq      f x := bind f fun y => Functor.map y (x ())
# end hidden
```

Notice here that `x` is our `(Unit → f α)` function, and it is calling that function by passing the
Unit value `()`.  All this just to ensure delayed evaluation.