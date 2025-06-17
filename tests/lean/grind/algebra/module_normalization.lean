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
