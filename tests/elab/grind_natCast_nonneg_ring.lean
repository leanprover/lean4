open Lean Grind Std
attribute [instance] Semiring.natCast

variable [Lean.Grind.CommRing R] [LE R] [LT R] [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R]

example (a : Nat) : 0 ≤ (a : R) := by
  grind

example (a b : Nat) : 0 ≤ (a : R) + (b : R) := by
  grind

example (a : Nat) : 0 ≤ 2 * (a : R) := by
  grind

example (a : Nat) : 0 ≥ -3 * (a : R) := by
  grind
