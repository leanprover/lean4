# Monads

Building on [Functors](functors.md) and [Applicatives](applicatives.md) we can now introduce
[monads](https://en.wikipedia.org/wiki/Monad_%28category_theory%29).

A monad is another type of abstract, functional structure. Let's explore what makes it different
from our first two structures.

## What is a Monad?

A monad is a computational context. It provides a structure that allows you to chain together
operations that have some kind of shared state or similar effect. Whereas pure functional code can
only operate on explicit input parameters and affect the program through explicit return values,
operations in a monad can affect other computations in the chain implicitly through side effects,
especially modification of an implicitly shared value.

# How are monads represented in Lean?

Like functors and applicatives, monads are represented with a type class in Lean:

```lean,ignore
class Monad (m : Type u → Type v) extends Applicative m, Bind m where
    ...
```

Just as every applicative is a functor, every monad is also an applicative and
there's one more new base type class used here that we need to explain, namely, `Bind`.

```lean
# namespace hidden
class Bind (f : Type u → Type v) where
  bind : {α β : Type u} → f α → (α → f β) → f β
# end hidden
```

The `bind` operator also has infix notation `>>=` where `x >>= g` represents the result of
executing `x` to get a value of type `f α` then unwrapping the value `α` from that and
passing it to function `g` of type `α → f β` returning the result of type `f β` where
`f` is our structure type (like Option or List)

This `bind` operation looks similar to the other ones we've seen so far, if we put
them all together Monad has the following operations:

```lean,ignore
class Monad (f : Type u → Type v) extends Applicative f, Bind f where
  pure {α : Type u} : α → f α
  map : {α β : Type u} → (α → β) → f α → f β
  seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β
  bind : {α β : Type u} → f α → (α → f β) → f β
  ...
```

Notice `Monad` also contains `pure` so a monad must also have a "default" way to wrap a value in the
structure.

The `bind` operator is similar to the applicative `seq` operator in that it chains two operations,
with one of them being function related.

Notice that `bind`, `seq` and `map` all take a function of some kind, and then a structure wrapped
over a type `α`, namely `f α`, and then produce a structure wrapping a type `β`, namely `f β`. They
just vary in what the function looks like. For the functor, the function is a normal pure function
because it has the type `(α → β)`. For applicatives, the function is still pure, but wrapped in the
structure `f (α → β)`. Now with monads, our function argument takes a "pure" input `α` but produces
an output in the structure, `(α → f β)`

## Basic Monad Example

Just as `Option` is a functor and an applicative functor, it is also a monad!
We can start with how `Option` implements the Monad type class.

```lean,ignore
instance : Monad Option where
  pure := Option.some
  bind := Option.bind
```

where:

```lean,ignore
def Option.bind : Option α → (α → Option β) → Option β
  | none,   _ => none
  | some a, f => f a
```

| Side note     |
| -------------- |
| this function definition is using a special shorthand syntax in Lean where the `:= match a, b with` code can be collapsed away. To make this more clear consider the following simpler example, where `Option.bind` is using the second form like `bar`: |
```lean
def foo (x : Option Nat) (y: Nat) : Option Nat :=
  match x, y with
  | none, _ => none
  | some x, y => some (x + y)

def bar : Option Nat → Nat → Option Nat
  | none, _ => none
  | some x, y => some (x + y)

#eval foo (some 1) 2
#eval bar (some 1) 2
```

What is important is that `Option.bind` is using a `match` statement to unwrap the input value
`Option α`, if it is `none` then it does nothing and returns `none`, if it has a value of type `α`
then it applies the function in the second argument `(α → Option β)` to this value, which is
the expression `f a` that you see in the line `  | some a, f => f a` above.  The function
returns a result of type `Option β` which then becomes the return value for `bind`.  So there
is no structure wrapping required on the return value since the input function already did that.

But let's bring in our definition of a monad. What does it mean to describe `Option` as a
computational context?

The `Option` monad encapsulates the context of failure. Essentially, the `Option` monad lets us
abort a series of operations whenever one of them fails. This allows future operations to assume
that all previous operations have succeeded. Here's some code to motivate this idea:

```lean
def maybeFunc1 : String -> Option Nat
| "" => none
| str => some str.length

def maybeFunc2 (i : Nat) : Option Float :=
  if i % 2 == 0 then none else some (i.toFloat * 3.14159)

def maybeFunc3 (f : Float) : Option (List Nat) :=
  if f > 15.0 then none else some [f.floor.toUInt32.toNat, f.ceil.toUInt32.toNat]

def runMaybeFuncs (input : String) : Option (List Nat) :=
  match maybeFunc1 input with
  | none => none
  | some i => match maybeFunc2 i with
    | none => none
    | some f => maybeFunc3 f

#eval runMaybeFuncs "big" -- some [9, 10]
```

We have three different functions that could fail. We combine them all in `runMaybeFuncs`. But at each
stage, it has to check if the previous result succeeded. It would be very tedious to continue this
pattern.

The `Option` monad helps you fix this. Here's what this function looks like using the `bind` operator.

```lean
# ++
def runMaybeFuncsBind (input: String) : Option (List Nat) :=
  maybeFunc1 input >>= maybeFunc2 >>= maybeFunc3

#eval runMaybeFuncsBind "big" -- some [9, 10]
```

It's much cleaner now! We take our first result and pass it into the second and third functions
using the bind function. The monad instance handles all the failure cases so we don't have to!

Let's see why the types work out. The result of `maybeFunc1` input is simply `Option Nat`. Then the
bind operator allows you to take this `Option Nat` value and combine it with `maybeFunc2`, whose type
is `Nat → Option Float` The **bind operator resolves** these to an `Option Float`. Then we pass this
similarly through the bind operator to `maybeFunc3`, resulting in our final type, `Option (List Nat)`.

Your functions will not always combine so cleanly though. This is where `do` notation comes into play.
This notation allows you to write monadic operations one after another, line-by-line. It almost makes
our code look like imperative programming. We can rewrite the above as:

```lean
# ++
def runMaybeFuncsDo (input: String) : Option (List Nat) := do
  let i ← maybeFunc1 input
  let f ← maybeFunc2 i
  maybeFunc3 f

#eval runMaybeFuncsDo "big" -- some [9, 10]
```

Note you can use `<-` or the nice unicode symbol `←` which you can type into VS code by typing
these characters `\<- `.  When you type the final space, `\<-` is replaced with `←`.

The `←` operator is special. It effectively unwraps the value on the right-hand side from the monad.
This means the value `i` has type `Nat`, _even though_ the result of `maybeFunc1` is `Option Nat`.
The bind operation happens under the hood. If the function returns `none`, then the entire
`runMaybeFuncsDo` function will return `none`. Observe that we do not unwrap the final line of the
computation. Our function result is `Option (List Nat)` which matches what `maybeFunc3` returns.

At first glance, this looks more complicated than the bind example. However, it gives you a lot more
flexibility, like mixing monadic and non-monadic statements. It is particularly helpful when one
monadic function depends on multiple previous functions.

## Example using List

You can easily make `List` into a monad with the following, since List already provides an
implementation of `pure` and `bind`.

```lean
instance : Monad List  where
  pure := List.pure
  bind := List.bind
```

Like we saw with the applicative `seq` operator, the `bind` operator applies the given function
to every element of the list.  It is useful to look at the bind implementation for List:

```lean
# ++
# namespace hidden
open List
def bind (a : List α) (b : α → List β) : List β := join (map b a)
# end hidden
```

So `Functor.map` is used to apply the function `b` to every element of `a` but this would
return a whole bunch of little lists, so `join` is used to turn those back into a single list.

Here's an example where we use `bind` to convert a list of strings into a combined list of chars:

```lean
# ++
#eval "apple".toList  -- ['a', 'p', 'p', 'l', 'e']

#eval ["apple", "orange"] >>= String.toList
-- ['a', 'p', 'p', 'l', 'e', 'o', 'r', 'a', 'n', 'g', 'e']
```

List also provides some functions that are designed to operate in the context of a monad.
These methods end in upper case M like this one:

```lean
# ++
def hasSomeItemGreaterThan (x : List Nat) (n: Nat): Option Bool := do
  x >>= List.anyM (λ a => if a > n then true else false)

#eval hasSomeItemGreaterThan [0, 0, 1, 0, 1, 0, 1, 2] 1 -- some true
#eval hasSomeItemGreaterThan [0, 0, 1, 0, 1, 0, 1, 2] 10 -- some false
#eval hasSomeItemGreaterThan [] 5 -- some false
```


## The IO Monad

The `IO Monad` is perhaps the most important monad in Lean. It is also one of the hardest monads to
understand starting out. Its actual implementation is too intricate to discuss when first learning
monads. So we'll learn by example.

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

When you function is `IO` monadic, you can get any input you need, call into "pure" code with the
inputs, and then output the result in some way. The reverse does not work. You cannot call into IO
code from pure code like you can call into a function that takes `Option` as input. Another way to
say this is you cannot invent an `IO` context out of thin air, it has to be given to you in your
`main` function.

Let's look at a simple program showing a few of the basic IO functions. We'll use `do` notation so you
can see how it is similar to the `Option` monad. We list the types of each IO function for clarity.


```lean
def main : IO Unit := do
  IO.println "enter a line of text:"
  let stdin ← IO.getStdin
  let input ← stdin.getLine
  let uppercased := input.toUpper
  IO.println uppercased
```

So, once again we see that the `do` notation lets you chain a series of monadic actions.
`IO.getStdin` is of type `IO IO.FS.Stream` and `stdin.getLine` is of type `IO String`
and `IO.println` is of type `IO Unit`

Note: a let statement can occur in any monad. Just as we could unwrap `i` from `Option Nat` to get the
inner Nat, we can use `←` to unwrap the result of `getLine` to get a String. We can then manipulate
this value using normal pure string functions like `toUpper`, and then we can pass the result to the
print function.

This is a simple echo program. It reads a line from the terminal, and then prints the line back out
capitalized to the terminal. Hopefully it gives you a basic understanding of how IO works.

You can test this program using `lean --run` as follows:

```
> lean --run Main.lean
enter a line of text:
the quick brown fox
THE QUICK BROWN FOX
```

Here we entered the string `the quick brown fox` and got back the uppercase result.

## What separates Monads from Applicatives?

The key word that separates these is **context**. We cannot really determine the structure of
"future" operations without knowing the results of "past" operations, because the past can alter the
context in which the future operations work. With applicatives, we can't get the final function
result without evaluating everything, but we can determine the structure of how the operation will
take place. This allows some degree of parallelism with applicatives that is not generally possible
with monads.

## What are the Monad Laws?

Monads have two laws:

- Identity
- Associativity

### Identity

TBD: https://mmhaskell.com/monads/tutorial talks about "Left Identity" and "Right Identity"
but I don't see this in `LawfulMonad` in Lean but I do see this theorem

```lean
theorem bind_eq (x : Id α) (f : α → id β) : x >>= f = f x := by rfl
```

BUGBUG But I'm not sure how to turn this into a simple example...


### Associativity
```
(x : m α) (f : α → m β) (g : β → m γ) : x >>= f >>= g = x >>= (λ x => f x >>= g)
```

The associativity law is difficult to parse like some of the applicative laws, but what it is saying
is that if you change the grouping of `bind` operations, you should still get the same result. You
can see this in action in the following rewrite of `runMaybeFuncsBind`:

```lean
# ++
# def maybeFunc1 : String -> Option Nat
# | "" => none
# | str => some str.length
# def maybeFunc2 (i : Nat) : Option Float :=
#   if i % 2 == 0 then none else some (i.toFloat * 3.14159)
# def maybeFunc3 (f : Float) : Option (List Nat) :=
#   if f > 15.0 then none else some [f.floor.toUInt32.toNat, f.ceil.toUInt32.toNat]
def runMaybeFuncsBind2 (input: String) : Option (List Nat) :=
   maybeFunc1 input >>= (λ x => maybeFunc2 x >>= maybeFunc3)

#eval runMaybeFuncsBind2 "big" -- some [9, 10]
```

Unlike applicatives, we can't resolve the structure of later operations without the results of
earlier operations quite as well because of the extra context monads provide. But we can still group
their later operations into composite functions taking their inputs from earlier on, and the result
should be the same.

While these laws are difficult to understand just by looking at them, the good news is that most of
the instances you'll make of these classes will naturally follow the laws, so you don't have to
worry about them too much.

## Conclusion

Hopefully you now have a basic level understanding of what a monad is. But perhaps some more
examples of what a "computational context" means would be useful to you. The Reader, State
and Except monads each provide a concrete and easily understood context that can be compared easily
to function parameters. You can learn more about those in [Part 4: Reader monads](readers.md) and
[Part 5: State monads](states.md) and [Part 5: Except monad](except.md).
