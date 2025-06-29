open Lean.Grind

variable [CommRing R] [LinearOrder R] [OrderedRing R]
example (a b : R) (h : 0 ≤ a * b) : 0 ≤ b * a := by grind
example (a b : R) (h : 7 ≤ a * b) : 7 ≤ b * a := by grind

example (a b : Int) (h : 0 ≤ a * b) : 0 ≤ b * a := by grind
example (a b : Int) (h : 7 ≤ a * b) : 7 ≤ b * a := by grind

example (a b : Nat) (h : 0 ≤ a * b) : 0 ≤ b * a := by grind
example (a b : Nat) (h : 7 ≤ a * b) : 7 ≤ b * a := by grind
