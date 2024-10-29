/-!
# Applicative Functors

Building on [Functors](functors.lean.md) is the [Applicative
Functor](https://en.wikipedia.org/wiki/Applicative_functor). For simplicity, you can refer to these
simply as "Applicatives". These are a little tricker than functors, but still simpler than monads.
Let's see how they work!

## What is an Applicative Functor?

An applicative functor defines a default or "base" construction for an object and allows
function application to be chained across multiple instances of the structure. All applicative
functors are functors, meaning they must also support the "map" operation.

## How are Applicatives represented in Lean?

An [applicative functor](https://en.wikipedia.org/wiki/Applicative_functor) is an intermediate
structure between `Functor` and `Monad`. It mainly consists of two operations:

* `pure : α → F α`
* `seq : F (α → β) → F α → F β` (written as `<*>`)

The `pure` operator specifies how you can wrap a normal object `α` into an instance of this structure `F α`.
This is the "default" mechanism mentioned above.

The `seq` operator allows you to chain operations by wrapping a function in a structure. The name
"applicative" comes from the fact that you "apply" functions from within the structure, rather than
simply from outside the structure, as was the case with `Functor.map`.

Applicative in Lean is built on some helper type classes, `Functor`, `Pure` and `Seq`:

-/
namespace hidden -- hidden
class Applicative (f : Type u → Type v) extends Functor f, Pure f, Seq f, SeqLeft f, SeqRight f where
  map      := fun x y => Seq.seq (pure x) fun _ => y
  seqLeft  := fun a b => Seq.seq (Functor.map (Function.const _) a) b
  seqRight := fun a b => Seq.seq (Functor.map (Function.const _ id) a) b
end hidden -- hidden
/-!
Notice that as with `Functor` it is also a type transformer `(f : Type u → Type v)` and notice the
`extends Functor f` is ensuring the base `Functor` also performs that same type transformation.

As stated above, all applicatives are then functors. This means you can assume that `map` already
exists for all these types.

The `Pure` base type class is a very simple type class that supplies the `pure` function.

-/
namespace hidden -- hidden
class Pure (f : Type u → Type v) where
   pure {α : Type u} : α → f α
end hidden -- hidden
/-!

You can think of it as lifting the result of a pure value to some monadic type. The simplest example
of `pure` is the `Option` type:

-/
#eval (pure 10 : Option Nat)  -- some 10
/-!

Here we used the `Option` implementation of `pure` to wrap the `Nat 10` value in an `Option Nat`
type resulting in the value `some 10`, and in fact if you look at the Monad instance of `Option` , you
will see that `pure` is indeed implemented using `Option.some`:

-/
instance : Monad Option where
    pure := Option.some
/-!

The `Seq` type class is also a simple type class that provides the `seq` operator which can
also be written using the special syntax `<*>`.

-/
namespace hidden -- hidden
class Seq (f : Type u → Type v) : Type (max (u+1) v) where
  seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β
end hidden -- hidden
/-!


## Basic Applicative Examples

Many of the basic functors also have instances of `Applicative`.
For example, `Option` is also `Applicative`.

So let's take a look and what the `seq` operator can do.  Suppose you want to multiply two `Option Nat`
objects.  Your first attempt might be this:

-/
#check_failure (some 4) * (some 5)      -- failed to synthesize instance
/-!

You then might wonder how to use the `Functor.map` to solve this since you could do these before:

-/
#eval (some 4).map (fun x => x * 5)  -- some 20

#eval (some 4).map (· * 5)  -- some 20

#eval (· * 5) <$> (some 4)   -- some 20
/-!

Remember that `<$>` is the infix notation for `Functor.map`.

The functor `map` operation can apply a multiplication to the value in the `Option` and then lift the
result back up to become a new `Option` , but this isn't what you need here.

The `Seq.seq` operator `<*>` can help since it can apply a function to the items inside a
container and then lift the result back up to the desired type, namely `Option` .

There are two ways to do this:

-/
#eval pure (.*.) <*> some 4 <*> some 5 -- some 20

#eval (.*.) <$> some 4 <*> some 5 -- some 20
/-!

In the first way, we start off by wrapping the function in an applicative using pure. Then we apply
this to the first `Option` , and again to the second `Option`  in a chain of operations.  So  you can see
how `Seq.seq` can be chained in fact, `Seq.seq` is really all about chaining of operations.

But in this case there is a simpler way.  In the second way, you can see that "applying" a single
function to a container is the same as using `Functor.map`. So you use `<$>` to "transform" the first
option into an `Option` containing a function, and then apply this function over the second value.

Now if either side is `none`, the result is `none`, as expected, and in this case the
`seq` operator was able to eliminate the multiplication:

-/
#eval (.*.) <$> none <*> some 5  -- none
#eval (.*.) <$> some 4 <*> none  -- none
/-!

For a more interesting example, let's make `List` an applicative by adding the following
definition:

-/
instance : Applicative List where
  pure := List.singleton
  seq f x := List.flatMap f fun y => Functor.map y (x ())
/-!

Notice you can now sequence a _list_ of functions and a _list_ of items.
The trivial case of sequencing a singleton list is in fact the same as `map`, as you saw
earlier with the `Option`  examples:

-/
#eval [ (·+2)] <*> [4, 6] -- [6, 8]
#eval (·+2) <$> [4,6]    -- [6, 8]
/-!

But now with list it is easier to show the difference when you do this:

-/
#eval [(·+2), (· *3)] <*> [4, 6] -- [6, 8, 12, 18]
/-!

Why did this produce 4 values?  The reason is because `<*>` applies _every_ function to _every_
value in a pairwise manner.  This makes sequence really convenient for solving certain problems. For
example, how do you get the pairwise combinations of all values from two lists?

-/
#eval Prod.mk <$> [1, 2, 3] <*> [4, 5, 6]
-- [(1, 4), (1, 5), (1, 6), (2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6)]
/-!

How do you get the sum of these pairwise values?
-/
#eval (·+·) <$> [1, 2, 3] <*> [4, 5, 6]
-- [5, 6, 7, 6, 7, 8, 7, 8, 9]
/-!

Here you can use `<$>` to "transform" each element of the first list into a function, and then apply
these functions over the second list.

If you have 3 lists, and want to find all combinations of 3 values across those lists you
would need helper function that can create a tuple out of 3 values, and Lean provides a
very convenient syntax for that `(·,·,·)`:

-/
#eval (·,·,·) <$> [1, 2] <*> [3, 4] <*> [5, 6]
-- [(1, 3, 5), (1, 3, 6), (1, 4, 5), (1, 4, 6), (2, 3, 5), (2, 3, 6), (2, 4, 5), (2, 4, 6)]
/-!

And you could sum these combinations if you first define a sum function that takes three inputs and
then you could chain apply this over the three lists.  Again lean can create such a function
with the expression `(·+·+·)`:

-/
#eval (·+·+·) <$> [1, 2] <*> [3, 4] <*> [5, 6]
-- [9, 10, 10, 11, 10, 11, 11, 12]
/-!

And indeed each sum here matches the expected values if you manually sum the triples we
show above.

**Side note:** there is another way to combine lists with a function that does not do the pairwise
combinatorics, it is called `List.zipWith`:

-/
#eval List.zipWith (·+·) [1, 2, 3] [4, 5, 6]
-- [5, 7, 9]
/-!

And there is a helper function named `List.zip` that calls `zipWith` using the function `Prod.mk`
so you get a nice zipped list like this:

-/
#eval List.zip [1, 2, 3] [4, 5, 6]
-- [(1, 4), (2, 5), (3, 6)]
/-!

And of course, as you would expect, there is an `unzip` also:

-/
#eval List.unzip (List.zip [1, 2, 3] [4, 5, 6])
-- ([1, 2, 3], [4, 5, 6])
/-!

## Example: A Functor that is not Applicative

From the chapter on [functors](functors.lean.md) you might remember this example of `LivingSpace`
that had a `Functor` instance:

-/
structure LivingSpace (α : Type) where
  totalSize : α
  numBedrooms : Nat
  masterBedroomSize : α
  livingRoomSize : α
  kitchenSize : α
  deriving Repr, BEq

def LivingSpace.map (f : α → β) (s : LivingSpace α) : LivingSpace β :=
  { totalSize := f s.totalSize
    numBedrooms := s.numBedrooms
    masterBedroomSize := f s.masterBedroomSize
    livingRoomSize := f s.livingRoomSize
    kitchenSize := f s.kitchenSize }

instance : Functor LivingSpace where
  map := LivingSpace.map
/-!

It wouldn't really make sense to make an `Applicative` instance here. How would you write `pure` in
the `Applicative` instance? By taking a single value and plugging it in for total size _and_ the
master bedroom size _and_ the living room size? That wouldn't really make sense. And what would the
numBedrooms value be for the default? What would it mean to "chain" two of these objects together?

If you can't answer these questions very well, then it suggests this type isn't really an
Applicative functor.

## SeqLeft and SeqRight

You may remember seeing the `SeqLeft` and `SeqRight` base types on `class Applicative` earlier.
These provide the `seqLeft` and `seqRight` operations which also have some handy notation
shorthands `<*` and `*>` respectively. Where: `x <* y` evaluates `x`, then `y`, and returns the
result of `x` and `x *> y` evaluates `x`, then `y`,  and returns the result of `y`.

To make it easier to remember, notice that it returns that value that the `<*` or `*>` notation is
pointing at.  For example:

-/
#eval (some 1) *> (some 2) -- Some 2
#eval (some 1) <* (some 2) -- Some 1
/-!

So these are a kind of "discard" operation.  Run all the actions, but only return the values that you
care about. It will be easier to see these in action when you get to full Monads, but they are used
heavily in the Lean `Parsec` parser combinator library where you will find parsing functions like
this one which parses the XML declaration `<?xml version="1.0" encoding='utf-8' standalone="yes">`:

```lean
def XMLdecl : Parsec Unit := do
  skipString "<?xml"
  VersionInfo
  optional EncodingDecl *> optional SDDecl *> optional S *> skipString "?>"
```

But you will need to understand full Monads before this will make sense.

## Lazy Evaluation

Diving a bit deeper, (you can skip this and jump to the [Applicative
Laws](laws.lean.md#what-are-the-applicative-laws) if don't want to dive into this implementation detail right
now). But, if you write a simple `Option` example `(.*.) <$> some 4 <*> some 5` that produces `some 20`
using `Seq.seq` you will see something interesting:

-/
#eval Seq.seq ((.*.) <$> some 4) (fun (_ : Unit) => some 5) -- some 20
/-!

This may look a bit cumbersome, specifically, why did we need to invent this funny looking function
`fun (_ : Unit) => (some 5)`?

Well if you take a close look at the type class definition:
```lean
class Seq (f : Type u → Type v) where
  seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β
```

You will see this function defined here: `(Unit → f α)`, this is a function that takes `Unit` as input
and produces the output of type `f α` where `f` is the container type `Type u -> Type v`, in this example `Option`
and `α` is the element type `Nat`, so `fun (_ : Unit) => some 5` matches this definition because
it is taking an input of type Unit and producing `some 5` which is type `Option Nat`.

The that `seq` is defined this way is because Lean is an eagerly evaluated language
(call-by-value), you have to use this kind of Unit function whenever you want to explicitly delay
evaluation and `seq` wants that so it can eliminate unnecessary function evaluations whenever
possible.

Fortunately the `<*>` infix notation hides this from you by creating this wrapper function for you.
If you look up the notation using F12 in VS Code you will find it contains `(fun _ : Unit => b)`.

Now to complete this picture you will find the default implementation of `seq` on the Lean `Monad`
type class:

```lean
class Monad (m : Type u → Type v) extends Applicative m, Bind m where
  seq      f x := bind f fun y => Functor.map y (x ())
```

Notice here that `x` is the `(Unit → f α)` function, and it is calling that function by passing the
Unit value `()`, which is the Unit value (Unit.unit).  All this just to ensure delayed evaluation.

## How do Applicatives help with Monads?

Applicatives are helpful for the same reasons as functors. They're a relatively simple abstract
structure that has practical applications in your code. Now that you understand how chaining
operations can fit into a structure definition, you're in a good position to start learning about
[Monads](monads.lean.md)!
-/
