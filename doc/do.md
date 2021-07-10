# The `do` notation

Lean is a pure functional programming language, but you can write effectful code using the `do` embedded domain specific language (DSL). The following simple program prints two strings "hello" and "world" in the standard output and terminates with exit code 0. Note that the type of the program is `IO UInt32`. You can read this type as the type of values that perform input-output effects and produce a value of type `UInt32`.

```lean
def main : IO UInt32 := do
  IO.println "hello"
  IO.println "world"
  return 0
```
The type of `IO.println` is `String → IO Unit`. That is, it is a function from `String` to `IO Unit` which indicates it may perform input-output effects and produce a value of type `Unit`. We often say that functions that may perform effects are *methods*.
We also say a method application, such as `IO.println "hello"` is an *action*.
Note that the examples above also demonstrates that braceless `do` blocks are whitespace sensitive.
If you like `;`s and curly braces, you can write the example above as
```lean
def main : IO UInt32 := do {
  IO.println "hello";
  IO.println "world";
  return 0;
}
```
Semicolons can be used even when curly braces are not used. They are particularly useful when you want to "pack" more than one action in a single line.
```lean
def main : IO UInt32 := do
  IO.println "hello"; IO.println "world"
  return 0
```
Whitespace sensitivity in programming languages is a controversial topic
among programmers. You should use your own style. We, the Lean developers, **love** the
braceless and semicolon-free style.
We believe it is clean and beautiful.

The `do` DSL expands into the core Lean language. Let's inspect the different components using the commands `#print` and `#check`.

```lean
# def main : IO UInt32 := do
#  IO.println "hello"
#  IO.println "world"
#  return 0

#check IO.println "hello"
-- IO Unit
#print main
-- Output contains the infix operator `>>=` and `pure`
-- The following `set_option` disables notation such as `>>=` in the output
set_option pp.notation false in
#print main
-- Output contains `bind` and `pure`
#print bind
-- bind : {m : Type u → Type v} → [self : Bind m] → {α β : Type u} →
--        m α → (α → m β) → m β
#print pure
-- pure : {m : Type u → Type v} → [self : Pure m] → {α : Type u} →
--        α → m α

-- IO implements the type classes `Bind` and `Pure`.
#check (inferInstance : Bind IO)
#check (inferInstance : Pure IO)
```
The types of `bind` and `pure` may look daunting at first sight.
They both have many implicit arguments. Let's focus first on the explicit arguments.
`bind` has two explicit arguments `m α` and `α → m β`. The first one should
be viewed as an action with effects `m` and producing a value of type `α`.
The second is a function that takes a value of type `α` and produces an action
with effects `m` and a value of type `β`. The result is `m β`. The method `bind` is composing
these two actions. We often say `bind` is an abstract semicolon. The method `pure` converts
a value `α` into an action that produces an action `m α`.

Here is the same function being defined using `bind` and `pure` without the `do` DSL.
```lean
def main : IO UInt32 :=
  bind (IO.println "hello") fun _ =>
  bind (IO.println "world") fun _ =>
  pure 0
```

The notations `let x <- action1; action2` and `let x ← action1; action2` are just syntax sugar for `bind action1 fun x => action2`.
Here is a small example using it.
```lean
def isGreaterThan0 (x : Nat) : IO Bool := do
  IO.println s!"value: {x}"
  return x > 0

def f (x : Nat) : IO Unit := do
  let c <- isGreaterThan0 x
  if c then
    IO.println s!"{x} is greater than 0"
  else
    pure ()

#eval f 10
-- value: 10
-- 10 is greater than 0
```


## Nested actions

Note that we cannot write `if isGreaterThan0 x then ... else ...` because the condition in a `if-then-else` is a **pure** value without effects, but `isGreaterThan0 x` has type `IO Bool`. You can use the nested action notation to avoid this annoyance. Here is an equivalent definition for `f` using a nested action.
```lean
# def isGreaterThan0 (x : Nat) : IO Bool := do
#  IO.println s!"x: {x}"
#  return x > 0

def f (x : Nat) : IO Unit := do
  if (<- isGreaterThan0 x) then
    IO.println s!"{x} is greater than 0"
  else
    pure ()

#print f
```
Lean "lifts" the nested actions and introduces the `bind` for us.
Here is an example with two nested actions. Note that both actions are executed
even if `x = 0`.
```lean
# def isGreaterThan0 (x : Nat) : IO Bool := do
#  IO.println s!"x: {x}"
#  return x > 0

def f (x y : Nat) : IO Unit := do
  if (<- isGreaterThan0 x) && (<- isGreaterThan0 y) then
    IO.println s!"{x} and {y} are greater than 0"
  else
    pure ()

#eval f 0 10
-- value: 0
-- value: 10

-- The function `f` above is equivalent to
def g (x y : Nat) : IO Unit := do
  let c1 <- isGreaterThan0 x
  let c2 <- isGreaterThan0 y
  if c1 && c2 then
    IO.println s!"{x} and {y} are greater than 0"
  else
    pure ()

theorem fgEqual : f = g :=
  rfl -- proof by reflexivity
```
Here are two ways to achieve the short-circuit semantics in the example above
```lean
# def isGreaterThan0 (x : Nat) : IO Bool := do
#  IO.println s!"x: {x}"
#  return x > 0

def f1 (x y : Nat) : IO Unit := do
  if (<- isGreaterThan0 x <&&> isGreaterThan0 y) then
    IO.println s!"{x} and {y} are greater than 0"
  else
    pure ()

-- `<&&>` is the effectful version of `&&`
-- Given `x y : IO Bool`, `x <&&> y` : m Bool`
-- It only executes `y` if `x` returns `true`.

#eval f1 0 10
-- value: 0
#eval f1 1 10
-- value: 1
-- value: 10
-- 1 and 10 are greater than 0

def f2 (x y : Nat) : IO Unit := do
  if (<- isGreaterThan0 x) then
    if (<- isGreaterThan0 y) then
      IO.println s!"{x} and {y} are greater than 0"
    else
      pure ()
  else
    pure ()
```

## `if-then` notation

In the `do` DSL, we can write `if c then action` as a shorthand for `if c then action else pure ()`. Here is the method `f2` using this shorthand.
```lean
# def isGreaterThan0 (x : Nat) : IO Bool := do
#  IO.println s!"x: {x}"
#  return x > 0

def f2 (x y : Nat) : IO Unit := do
  if (<- isGreaterThan0 x) then
    if (<- isGreaterThan0 y) then
      IO.println s!"{x} and {y} are greater than 0"
```

## Reassignments

When writing effectful code, it is natural to think imperatively.
For example, suppose we want to create an empty array `xs`,
add `0` if some condition holds, add `1` if another condition holds,
and then print it. In the following example, we use variable
"shadowing" to simulate this kind of "update".

```lean
def f (b1 b2 : Bool) : IO Unit := do
  let xs := #[]
  let xs := if b1 then xs.push 0 else xs
  let xs := if b2 then xs.push 1 else xs
  IO.println xs

#eval f true true
-- #[0, 1]
#eval f false true
-- #[1]
#eval f true false
-- #[0]
#eval f false false
-- #[]
```

We can use tuples to simulate updates on multiple variables.

```lean
def f (b1 b2 : Bool) : IO Unit := do
  let xs := #[]
  let ys := #[]
  let (xs, ys) := if b1 then (xs.push 0, ys) else (xs, ys.push 0)
  let (xs, ys) := if b2 then (xs.push 1, ys) else (xs, ys.push 1)
  IO.println s!"xs: {xs}, ys: {ys}"

#eval f true false
-- xs: #[0], ys: #[1]
```

We can also simulate the control-flow above using *join-points*.
A join-point is a `let` that is always tail called and fully applied.
The Lean compiler implements them using `goto`s.
Here is the same example using join-points.

```lean
def f (b1 b2 : Bool) : IO Unit := do
  let jp1 xs ys := IO.println s!"xs: {xs}, ys: {ys}"
  let jp2 xs ys := if b2 then jp1 (xs.push 1) ys else jp1 xs (ys.push 1)
  let xs := #[]
  let ys := #[]
  if b1 then jp2 (xs.push 0) ys else jp2 xs (ys.push 0)

#eval f true false
-- xs: #[0], ys: #[1]
```

You can capture complex control-flow using join-points.
The `do` DSL offers the variable reassignment feature to make this kind of code more comfortable to write. In the following example, the `mut` modifier at `let mut xs := #[]` indicates that variable `xs` can be reassigned. The example contains two reassignments `xs := xs.push 0` and `xs := xs.push 1`. The reassignments are compiled using join-points. There is no hidden state being updated.

```lean
def f (b1 b2 : Bool) : IO Unit := do
  let mut xs := #[]
  if b1 then xs := xs.push 0
  if b2 then xs := xs.push 1
  IO.println xs

#eval f true true
-- #[0, 1]
```
The notation `x <- action` reassigns `x` with the value produced by the action. It is equivalent to `x := (<- action)`

## Iteration

The `do` DSL provides a unified notation for iterating over datastructures. Here are a few examples.

```lean
def sum (xs : Array Nat) : IO Nat := do
  let mut s := 0
  for x in xs do
    IO.println s!"x: {x}"
    s := s + x
  return s

#eval sum #[1, 2, 3]
-- x: 1
-- x: 2
-- x: 3
-- 6

-- We can write pure code using the `do` DSL too.
def sum' (xs : Array Nat) : Nat := do
  let mut s := 0
  for x in xs do
    s := s + x
  return s

#eval sum' #[1, 2, 3]
-- 6

def sumEven (xs : Array Nat) : IO Nat := do
  let mut s := 0
  for x in xs do
    if x % 2 == 0 then
      IO.println s!"x: {x}"
      s := s + x
  return s

#eval sumEven #[1, 2, 3, 6]
-- x: 2
-- x: 6
-- 8

def splitEvenOdd (xs : List Nat) : IO Unit := do
  let mut evens := #[]
  let mut odds  := #[]
  for x in xs do
    if x % 2 == 0 then
      evens := evens.push x
    else
      odds := odds.push x
  IO.println s!"evens: {evens}, odds: {odds}"

#eval splitEvenOdd [1, 2, 3, 4]
-- evens: #[2, 4], odds: #[1, 3]

def findNatLessThan (x : Nat) (p : Nat → Bool) : IO Nat := do
  -- [:x] is notation for the range [0, x)
  for i in [:x] do
    if p i then
      return i -- `return` from the `do` block
  throw (IO.userError "value not found")

#eval findNatLessThan 10 (fun x => x > 5 && x % 4 == 0)
-- 8

def sumOddUpTo (xs : List Nat) (threshold : Nat) : IO Nat := do
  let mut s := 0
  for x in xs do
    if x % 2 == 0 then
      continue -- it behaves like the `continue` statement in imperative languages
    IO.println s!"x: {x}"
    s := s + x
    if s > threshold then
      break -- it behaves like the `break` statement in imperative languages
  IO.println s!"result: {s}"
  return s

#eval sumOddUpTo [2, 3, 4, 11, 20, 31, 41, 51, 107] 40
-- x: 3
-- x: 11
-- x: 31
-- result: 45
-- 45
```

TODO: describe `forIn`

## Try-catch

TODO

## Pattern matching

TODO

## Monads

TODO

## ReaderT

TODO

## StateT

TODO

## StateRefT

TODO

## ExceptT

TODO

## MonadLift and automatic lifting

TODO
