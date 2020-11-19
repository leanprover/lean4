# What is Lean

Lean is a functional programming language that makes it easy to
write correct and maintainable code.

Lean programming primarily involves defining types and functions.
This allows your focus to remain on the problem domain and manipulating its data,
rather than the details of programming.

```lean
-- Defines a function that takes a name and produces a greeting.
def getGreeting (name : String) := "Hello, {name}! Isn't Lean great?"

-- The `main` function is the entry point of your program.
-- Its type is `IO Unit` because it can perform `IO` operations.
def main : IO Unit :=
  -- Defines a list of names
  let names := ["Sebastian", "Leo", "Daniel"]

  -- Print the list of greetings `names.map getGreeting`
  for greeting in names.map getGreeting do
    IO.println greeting
```

Lean has numerous features, including:

- Type inference
- First-class functions
- Powerful data types
- Pattern matching
- Type classes
- Extensible syntax
- Hygienic macros
- Dependent types
- Metaprogramming framework
- Async programming
- Verification, you can prove properties of your functions using Lean itself

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