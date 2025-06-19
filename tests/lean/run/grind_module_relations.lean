-- Tests for `grind` as solver for linear equations in an `IntModule` or `RatModule`.

open Lean.Grind

section IntModule

variable (R : Type u) [IntModule R]

-- In an `IntModule`, we should be able to handle relations
-- this is harder, and less important, than being able to do this in `RatModule`.
example (a b : R) (h : a + b = 0) : 3 * a - 7 * b = 9 * a + a := by grind
example (a b c : R) (h : 2 * a + 2 * b = 4 * c) : 3 * a + c = 5 * c - b + (-b) + a := by grind

end IntModule

section RatModule

variable (R : Type u) [IntModule R] [NoNatZeroDivisors R]

example (a b : R) (h : a + b = 0) : 3 * a - 7 * b = 9 * a + a := by grind
example (a b c : R) (h : 2 * a + 2 * b = 4 * c) : 3 * a + c = 5 * c - b + (-b) + a := by grind

-- In a `RatModule` we can clear common divisors.
example (a : R) (h : a + a = 0) : a = 0 := by grind
example (a b c : R) (h : 2 * a + 2 * b = 4 * c) : 3 * a + c = 7 * c - 3 * b := by grind

end RatModule
