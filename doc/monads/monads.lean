/-!
# Monads

Building on [Functors](functors.lean.md) and [Applicatives](applicatives.lean.md) we can now
introduce [monads](https://en.wikipedia.org/wiki/Monad_%28category_theory%29).

A monad is another type of abstract, functional structure. Let's explore what makes it different
from the first two structures.

## What is a Monad?

A monad is a computational context. It provides a structure that allows you to chain together
operations that have some kind of shared state or similar effect. Whereas pure functional code can
only operate on explicit input parameters and affect the program through explicit return values,
operations in a monad can affect other computations in the chain implicitly through side effects,
especially modification of an implicitly shared value.

## How are monads represented in Lean?

Like functors and applicatives, monads are represented with a type class in Lean:

```lean,ignore
class Monad (m : Type u → Type v) extends Applicative m, Bind m where
```

Just as every applicative is a functor, every monad is also an applicative and there's one more new
base type class used here that you need to understand, namely, `Bind`.

```lean,ignore
class Bind (f : Type u → Type v) where
  bind : {α β : Type u} → f α → (α → f β) → f β
```

The `bind` operator also has infix notation `>>=` where `x >>= g` represents the result of executing
`x` to get a value of type `f α` then unwrapping the value `α` from that and passing it to function
`g` of type `α → f β` returning the result of type `f β` where `f` is the target structure type
(like `Option` or List)

This `bind` operation looks similar to the other ones you've seen so far, if you put them all
together `Monad` has the following operations:

```lean,ignore
class Monad (f : Type u → Type v) extends Applicative f, Bind f where
  pure {α : Type u} : α → f α
  map : {α β : Type u} → (α → β) → f α → f β
  seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β
  bind : {α β : Type u} → f α → (α → f β) → f β
  ...
```

Notice `Monad` also contains `pure` it must also have a "default" way to wrap a value in the
structure.

The `bind` operator is similar to the applicative `seq` operator in that it chains two operations,
with one of them being function related. Notice that `bind`, `seq` and `map` all take a function of
some kind.  Let's examine those function types:

- map: `(α → β)`
- seq: `f (α → β)`
- bind: `(α → f β)`

So `map` is a pure function, `seq` is a pure function wrapped in the structure, and `bind` takes a
pure input but produces an output wrapped in the structure.

Note: we are ignoring the `(Unit → f α)` function used by `seq` here since that has a special
purpose explained in [Applicatives Lazy Evaluation](applicatives.lean.md#lazy-evaluation).

## Basic Monad Example

Just as `Option` is a functor and an applicative functor, it is also a monad! Let's start with how
`Option` implements the Monad type class.

-/
instance : Monad Option where
  pure := Option.some
  bind := Option.bind
/-!

where:

```lean,ignore
def Option.bind : Option α → (α → Option β) → Option β
  | none,   _ => none
  | some a, f => f a
```

> **Side note**: this function definition is using a special shorthand syntax in Lean where the `:=
match a, b with` code can be collapsed away. To make this more clear consider the following simpler
example, where `Option.bind` is using the second form like `bar`:

-/
def foo (x : Option Nat) (y : Nat) : Option Nat :=
  match x, y with
  | none, _ => none
  | some x, y => some (x + y)

def bar : Option Nat → Nat → Option Nat
  | none, _ => none
  | some x, y => some (x + y)

#eval foo (some 1) 2  -- some 3
#eval bar (some 1) 2  -- some 3
/-!
What is important is that `Option.bind` is using a `match` statement to unwrap the input value
`Option α`, if it is `none` then it does nothing and returns `none`, if it has a value of type `α`
then it applies the function in the second argument `(α → Option β)` to this value, which is
the expression `f a` that you see in the line `  | some a, f => f a` above.  The function
returns a result of type `Option β` which then becomes the return value for `bind`.  So there
is no structure wrapping required on the return value since the input function already did that.

But let's bring in the definition of a monad. What does it mean to describe `Option` as a
computational context?

The `Option` monad encapsulates the context of failure. Essentially, the `Option` monad lets us
abort a series of operations whenever one of them fails. This allows future operations to assume
that all previous operations have succeeded. Here's some code to motivate this idea:

-/
def optionFunc1 : String -> Option Nat
  | "" => none
  | str => some str.length

def optionFunc2 (i : Nat) : Option Float :=
  if i % 2 == 0 then none else some (i.toFloat * 3.14159)

def optionFunc3 (f : Float) : Option (List Nat) :=
  if f > 15.0 then none else some [f.floor.toUInt32.toNat, f.ceil.toUInt32.toNat]

def runOptionFuncs (input : String) : Option (List Nat) :=
  match optionFunc1 input with
  | none => none
  | some i => match optionFunc2 i with
    | none => none
    | some f => optionFunc3 f

#eval runOptionFuncs "big" -- some [9, 10]
/-!

Here you see three different functions that could fail. These are then combined in `runOptionFuncs`.
But then you have to use nested `match` expressions to check if the previous result succeeded. It
would be very tedious to continue this pattern much longer.

The `Option` monad helps you fix this. Here's what this function looks like using the `bind`
operator.

-/

def runOptionFuncsBind (input : String) : Option (List Nat) :=
  optionFunc1 input >>= optionFunc2 >>= optionFunc3

#eval runOptionFuncsBind "big" -- some [9, 10]
/-!

It's much cleaner now! You take the first result and pass it into the second and third functions
using the `bind` operation. The monad instance handles all the failure cases so you don't have to!

Let's see why the types work out. The result of `optionFunc1` input is simply `Option Nat`. Then the
bind operator allows you to take this `Option Nat` value and combine it with `optionFunc2`, whose type
is `Nat → Option Float` The **bind operator resolves** these to an `Option Float`. Then you pass this
similarly through the bind operator to `optionFunc3`, resulting in the final type, `Option (List Nat)`.

Your functions will not always combine so cleanly though. This is where `do` notation comes into play.
This notation allows you to write monadic operations one after another, line-by-line. It almost makes
your code look like imperative programming. You can rewrite the above as:
-/

def runOptionFuncsDo (input : String) : Option (List Nat) := do
  let i ← optionFunc1 input
  let f ← optionFunc2 i
  optionFunc3 f

#eval runOptionFuncsDo "big" -- some [9, 10]
/-!

The `←` operator used here is special. It effectively unwraps the value on the right-hand side from
the monad. This means the value `i` has type `Nat`, _even though_ the result of `optionFunc1` is
`Option Nat`. This is done using a `bind` operation under the hood.

> Note you can use `<-` or the nice unicode symbol `←` which you can type into VS code by typing
these characters `\l `.  When you type the final space, `\l` is replaced with `←`.

Observe that we do not unwrap the final line of the computation. The function result is `Option
(List Nat)` which matches what `optionFunc3` returns. At first glance, this may look more complicated
than the `bind` example. However, it gives you a lot more flexibility, like mixing monadic and
non-monadic statements, using if then/else structures with their own local do blocks and so on. It
is particularly helpful when one monadic function depends on multiple previous functions.

## Example using List

You can easily make `List` into a monad with the following, since List already provides an
implementation of `pure` and `bind`.

-/
instance : Monad List  where
  pure := List.singleton
  bind := List.flatMap
/-!

Like you saw with the applicative `seq` operator, the `bind` operator applies the given function
to every element of the list.  It is useful to look at the bind implementation for List:

-/
open List
def bind (a : List α) (b : α → List β) : List β := join (map b a)
/-!

So `Functor.map` is used to apply the function `b` to every element of `a` but this would
return a whole bunch of little lists, so `join` is used to turn those back into a single list.

Here's an example where you use `bind` to convert a list of strings into a combined list of chars:

-/

#eval "apple".toList  -- ['a', 'p', 'p', 'l', 'e']

#eval ["apple", "orange"] >>= String.toList
-- ['a', 'p', 'p', 'l', 'e', 'o', 'r', 'a', 'n', 'g', 'e']

/-!


## The IO Monad

The `IO Monad` is perhaps the most important monad in Lean. It is also one of the hardest monads to
understand starting out. Its actual implementation is too intricate to discuss when first learning
monads. So it is best to learn by example.

What is the **computational context** that describes the IO monad? IO operations can read
information from or write information to the terminal, file system, operating system, and/or
network. They interact with systems outside of your program. If you want to get user input, print a
message to the user, read information from a file, or make a network call, you'll need to do so
within the IO Monad.

The state of the world outside your program can change at virtually any moment, and so this IO
context is particularly special. So these IO operations are "side effects" which means you cannot
perform them from "pure" Lean functions.

Now, the most important job of pretty much any computer program is precisely to perform this
interaction with the outside world. For this reason, the root of all executable Lean code is a
function called main, with the type `IO Unit`. So every program starts in the IO monad!

When your function is `IO` monadic, you can get any input you need, call into "pure" code with the
inputs, and then output the result in some way. The reverse does not work. You cannot call into IO
code from pure code like you can call into a function that takes `Option` as input. Another way to
say this is you cannot invent an `IO` context out of thin air, it has to be given to you in your
`main` function.

Let's look at a simple program showing a few of the basic IO functions. It also uses `do` notation
to make the code read nicely:
-/
def main : IO Unit := do
  IO.println "enter a line of text:"
  let stdin ← IO.getStdin            -- IO IO.FS.Stream (monadic)
  let input ← stdin.getLine          -- IO.FS.Stream → IO String (monadic)
  let uppercased := input.toUpper    -- String → String (pure)
  IO.println uppercased              -- IO Unit (monadic)
/-!

So, once again you can see that the `do` notation lets you chain a series of monadic actions.
`IO.getStdin` is of type `IO IO.FS.Stream` and `stdin.getLine` is of type `IO String`
and `IO.println` is of type `IO Unit`.

In between you see a non-monadic expression `let uppercased := input.toUpper` which is fine too.
A let statement can occur in any monad. Just as you could unwrap `i` from `Option Nat` to get the
inner Nat, you can use `←` to unwrap the result of `getLine` to get a String. You can then manipulate
this value using normal pure string functions like `toUpper`, and then you can pass the result to the
`IO.println` function.

This is a simple echo program. It reads a line from the terminal, and then prints the line back out
capitalized to the terminal. Hopefully it gives you a basic understanding of how IO works.

You can test this program using `lean --run` as follows:

```
> lean --run Main.lean
enter a line of text:
the quick brown fox
THE QUICK BROWN FOX
```

Here the user entered the string `the quick brown fox` and got back the uppercase result.

## What separates Monads from Applicatives?

The key that separates these is **context**. You cannot really determine the structure of
"future" operations without knowing the results of "past" operations, because the past can alter the
context in which the future operations work. With applicatives, you can't get the final function
result without evaluating everything, but you can determine the structure of how the operation will
take place. This allows some degree of parallelism with applicatives that is not generally possible
with monads.


## Conclusion

Hopefully you now have a basic level understanding of what a monad is. But perhaps some more
examples of what a "computational context" means would be useful to you. The Reader, State and
Except monads each provide a concrete and easily understood context that can be compared easily to
function parameters. You can learn more about those in [Reader monads](readers.lean.md),
[State monads](states.lean.md), and the [Except monad](except.lean.md).
-/
