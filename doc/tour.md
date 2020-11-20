# Tour of Lean

The best way to learn about Lean is to read and write Lean code.
This article will act as a tour through some of the key features of the Lean
language and give you some code snippets that you can execute on your machine.
To learn about setting up a development environment, check out [Getting Started](./gettingStarted.md).

There are two primary concepts in Lean: functions and types.
This tour will emphasize features of the language which fall into
these two concepts.

# Functions and Namespaces

The most fundamental pieces of any Lean program are functions organized into namespaces.
[Functions](./functions.md) perform work on inputs to produce outputs,
and they are organized under [namespaces](./namespaces.md),
which are the primary way you group things in Lean.
They are defined using the [`def`](./definitions.md) command,
which give the function a name and define its arguments.

```lean
namespace BasicFunctions

-- The `#eval` command is used to evaluate expressions
#eval 2+2

-- You use 'def' to define a function. This one accepts a natural number
-- and returns a natural number.
-- Parentheses are optional for function arguments, except for when
-- you use an explicit type annotation.
-- Lean can often infer the type of the functions arguments
def sampleFunction1 x := x*x + 3

-- Apply the function, naming the function return result using 'def'.
-- The variable type is inferred from the function return type.
def result1 := sampleFunction1 4573

-- This line uses an interpolated string to print the result. Expressions inside
-- braces `{}` are converted into string using the polymorphic method `toString`
#eval println! "The result of squaring the integer 4573 and adding 3 is {result1}"

-- When needed, annotate the type of a parameter name using '(argument:type)'.
-- Parentheses are required.
def sampleFunction2 (x : Nat) := 2*x*x - x + 3

def result2 := sampleFunction2 (7 + 4)

#eval println! "The result of applying the 2nd sample function to (7 + 4) is {result2}"

-- Conditionals use if/then/else
def sampleFunction3 (x : Int) :=
  if x > 100 then
    2*x*x - x + 3
  else
    2*x*x + x - 37

#eval println! "The result of applying sampleFunction3 to 2 is {sampleFunction3 2}"

end BasicFunctions
```

```lean
-- Lean has first class functions
-- `twice` takes two argumes `f` and `a` where
-- `f` is a function from natural numbers to natural numbers, and
-- `a` is a natural number
def twice (f : Nat → Nat) (a : Nat) :=
  f (f a)

-- `fun` is to declare anonymous functions
#eval twice (fun x => x + 2) 10

-- You prove theorems about your functions.
-- The following theorem states that for any natural number `a`,
-- adding 2 twice produces a value equal to `a + 4`.
theorem twiceAdd2 (a : Nat) : twice (fun x => x + 2) a = a + 4 :=
  -- The proof is by reflexivity. Lean "symbolic" reduces both sides of the equality
  -- and obtain the same result
  rfl

-- `(. + 2)` is syntax sugar for `(fun x => x + 2)`. The parentheses + `.` notation
-- is useful for defining simple functions
#eval twice (. + 2) 10

-- An enumerated type is a special case of inductive type in Lean
-- The following command creates a new type `Weekday`
inductive Weekday :=
  | sunday    : Weekday
  | monday    : Weekday
  | tuesday   : Weekday
  | wednesday : Weekday
  | thursday  : Weekday
  | friday    : Weekday
  | saturday  : Weekday

-- `Weekday` has 7 constructors/elements.
-- The constructors live in the `Weekday` namespace
-- Think of `sunday`, `monday`, …, saturday as being distinct elements of `Weekday`,
-- with no other distinguishing properties.
-- The command `#check` return the type of a term in Lean
#check Weekday.sunday
#check Weekday.monday

-- The `open` command opens a namespace
open Weekday
#check sunday
#check tuesday

-- You can define functions by pattern matching.
-- The following function converts a `Weekday` into a natural number.
def natOfWeekday (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

-- The `#eval` command evaluates an expression and prints the result.
#eval natOfWeekday tuesday

def isMonday : Weekday → Bool :=
  -- `fun` + `match`  is a common idiom.
  -- The the following expression is syntax sugar for
  -- fun d => match d with | monday => true | _ => false
  fun | monday => true | _ => false

#eval isMonday monday
#eval isMonday sunday

-- Lean has support for type classes and polymorphic methods.
-- The `toString` method converts a value into a `String`.
#eval toString 10
#eval toString (10, 20)

-- The method `toString` converts values of any type that implements
-- the class `ToString`.
-- You can implement instances of `ToString` for your own types.
instance : ToString Weekday := {
  toString := fun
    | sunday    => "Sunday"
    | monday    => "Monday"
    | tuesday   => "Tuesday"
    | wednesday => "Wednesday"
    | thursday  => "Thursday"
    | friday    => "Friday"
    | saturday  => "Saturday"
}

#eval toString (sunday, 10)

def Weekday.next : Weekday -> Weekday :=
  fun d => match d with
    | sunday    => monday
    | monday    => tuesday
    | tuesday   => wednesday
    | wednesday => thursday
    | thursday  => friday
    | friday    => saturday
    | saturday  => sunday

#eval Weekday.next Weekday.wednesday
-- Since `Weekday` namespace has already been opened, you can write.
#eval next wednesday

-- The idiom `fun d => match d with ...` used in the previous definition
-- is so common that Lean provides a syntax sugar for it. The foolowing
-- function uses it.
def Weekday.previous : Weekday -> Weekday
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

#eval next (previous wednesday)

-- We can prove that for any `Weekday` `d`, `next (previous d) = d`
theorem Weekday.nextOfPrevious (d : Weekday) : next (previous d) = d :=
  match d with
  | sunday    => rfl
  | monday    => rfl
  | tuesday   => rfl
  | wednesday => rfl
  | thursday  => rfl
  | friday    => rfl
  | saturday  => rfl

-- You can automate definitions such  as `Weekday.nextOfPrevious`
-- using metaprogramming
theorem Weekday.nextOfPrevious' (d : Weekday) : next (previous d) = d := by
  cases d -- A proof by cases
  repeat rfl -- Each case is solved using `rfl`
```
