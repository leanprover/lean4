-- Tests for `grind` as a module normalization tactic, when only `NatModule`, `IntModule`, or `RatModule` is available.

open Lean.Grind

section NatModule

variable (R : Type u) [NatModule R]

example (a b : R) : a + b = b + a := by grind
example (a : R) : a + 0 = a := by grind
example (a : R) : 0 + a = a := by grind
example (a b c : R) : a + b + c = a + (b + c) := by grind
example (a : R) : 2 * a = a + a := by grind
example (a b : R) : 2 * (b + c) = c + 2 * b + c := by grind

end NatModule

section IntModule

variable (R : Type u) [IntModule R]

example (a b : R) : a + b = b + a := by grind
example (a : R) : a + 0 = a := by grind
example (a : R) : 0 + a = a := by grind
example (a b c : R) : a + b + c = a + (b + c) := by grind
example (a : R) : 2 * a = a + a := by grind
example (a : R) : (-2 : Int) * a = -a - a := by grind
example (a b : R) : 2 * (b + c) = c + 2 * b + c := by grind
example (a b c : R) : 2 * (b + c) - 3 * c + b + b = c + 5 * b - 2 * c := by grind
example (a b c : R) : 2 * (b + c) + (-3 : Int) * c + b + b = c + (5 : Int) * b - 2 • c := by grind

end IntModule
