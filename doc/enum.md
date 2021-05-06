# Enumerated Types

The simplest kind of inductive type is simply a type with a finite, enumerated list of elements.
The following command declares the enumerated type `Weekday`.
```lean
inductive Weekday where
  | sunday    : Weekday
  | monday    : Weekday
  | tuesday   : Weekday
  | wednesday : Weekday
  | thursday  : Weekday
  | friday    : Weekday
  | saturday  : Weekday
```

The `Weekday` type has 7 constructors/elements. The constructors live in the `Weekday` namespace
Think of `sunday`, `monday`, …, `saturday` as being distinct elements of `Weekday`,
with no other distinguishing properties.
```lean
# inductive Weekday where
#  | sunday    : Weekday
#  | monday    : Weekday
#  | tuesday   : Weekday
#  | wednesday : Weekday
#  | thursday  : Weekday
#  | friday    : Weekday
#  | saturday  : Weekday
#check Weekday.sunday   -- Weekday
#check Weekday.monday   -- Weekday
```

You can define functions by pattern matching.
The following function converts a `Weekday` into a natural number.
```lean
# inductive Weekday where
#  | sunday    : Weekday
#  | monday    : Weekday
#  | tuesday   : Weekday
#  | wednesday : Weekday
#  | thursday  : Weekday
#  | friday    : Weekday
#  | saturday  : Weekday
def natOfWeekday (d : Weekday) : Nat :=
  match d with
  | Weekday.sunday    => 1
  | Weekday.monday    => 2
  | Weekday.tuesday   => 3
  | Weekday.wednesday => 4
  | Weekday.thursday  => 5
  | Weekday.friday    => 6
  | Weekday.saturday  => 7

#eval natOfWeekday Weekday.tuesday -- 3
```

It is often useful to group definitions related to a type in a namespace with the same name.
For example, we can put the function above into the ``Weekday`` namespace.
We are then allowed to use the shorter name when we open the namespace.

In the following example, we define functions from ``Weekday`` to ``Weekday`` in the namespace `Weekday`.
```lean
# inductive Weekday where
#  | sunday    : Weekday
#  | monday    : Weekday
#  | tuesday   : Weekday
#  | wednesday : Weekday
#  | thursday  : Weekday
#  | friday    : Weekday
#  | saturday  : Weekday
namespace Weekday

def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

end Weekday
```
It is so common to start a definition with a `match` in Lean, that Lean provides a syntax sugar for it.
```lean
# inductive Weekday where
#  | sunday    : Weekday
#  | monday    : Weekday
#  | tuesday   : Weekday
#  | wednesday : Weekday
#  | thursday  : Weekday
#  | friday    : Weekday
#  | saturday  : Weekday
# namespace Weekday
def previous : Weekday -> Weekday
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday
# end Weekday
```
We can use the command `#eval` to test our definitions.
```lean
# inductive Weekday where
#  | sunday    : Weekday
#  | monday    : Weekday
#  | tuesday   : Weekday
#  | wednesday : Weekday
#  | thursday  : Weekday
#  | friday    : Weekday
#  | saturday  : Weekday
# namespace Weekday
# def next (d : Weekday) : Weekday :=
#  match d with
#  | sunday    => monday
#  | monday    => tuesday
#  | tuesday   => wednesday
#  | wednesday => thursday
#  | thursday  => friday
#  | friday    => saturday
#  | saturday  => sunday
# def previous : Weekday -> Weekday
#  | sunday    => saturday
#  | monday    => sunday
#  | tuesday   => monday
#  | wednesday => tuesday
#  | thursday  => wednesday
#  | friday    => thursday
#  | saturday  => friday
def toString : Weekday -> String
  | sunday    => "Sunday"
  | monday    => "Monday"
  | tuesday   => "Tuesday"
  | wednesday => "Wednesday"
  | thursday  => "Thursday"
  | friday    => "Friday"
  | saturday  => "Saturday"

#eval toString (next sunday)             -- "Monday"
#eval toString (next tuesday)            -- "Wednesday"
#eval toString (previous wednesday)      -- "Tuesday"
#eval toString (next (previous sunday))  -- "Sunday"
#eval toString (next (previous monday))  -- "Monday"
-- ..
# end Weekday
```
We can now prove the general theorem that ``next (previous d) = d`` for any weekday ``d``.
The idea is to perform a proof by cases using `match`, and rely on the fact for each constructor both
sides of the equality reduce to the same term.
```lean
# inductive Weekday where
#  | sunday    : Weekday
#  | monday    : Weekday
#  | tuesday   : Weekday
#  | wednesday : Weekday
#  | thursday  : Weekday
#  | friday    : Weekday
#  | saturday  : Weekday
# namespace Weekday
# def next (d : Weekday) : Weekday :=
#  match d with
#  | sunday    => monday
#  | monday    => tuesday
#  | tuesday   => wednesday
#  | wednesday => thursday
#  | thursday  => friday
#  | friday    => saturday
#  | saturday  => sunday
# def previous : Weekday -> Weekday
#  | sunday    => saturday
#  | monday    => sunday
#  | tuesday   => monday
#  | wednesday => tuesday
#  | thursday  => wednesday
#  | friday    => thursday
#  | saturday  => friday
theorem nextOfPrevious (d : Weekday) : next (previous d) = d :=
  match d with
  | sunday    => rfl
  | monday    => rfl
  | tuesday   => rfl
  | wednesday => rfl
  | thursday  => rfl
  | friday    => rfl
  | saturday  => rfl
# end Weekday
```
