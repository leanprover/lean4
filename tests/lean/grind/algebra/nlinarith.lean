open Std Lean.Grind

-- TODO which other systems, e.g. Mathematica, Isabelle, nlia, can handle these?

variable (R : Type) [CommRing R] [LE R] [LT R] [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R]

example (a : R) : 0 ≤ a^2 := by grind
example (a : R) : 0 ≤ a^6 := by grind
example (a b : R) (_ : 0 ≤ a) (_ : 0 ≤ b) : 0 ≤ a * b := by grind
example (a b : R) (_ : a ≤ 0) (_ : 0 ≤ b) : a * b ≤ 0 := by grind
example (a b c : R) (_ : 0 ≤ a) (_ : b ≤ c) : a * b ≤ a * c := by grind
example (a b : R) (_ : 1 ≤ a) (_ : 1 ≤ b) : 1 ≤ a * b := by grind
example (a b : R) (_ : 3 ≤ a) (_ : 4 ≤ b) : 12 ≤ a * b := by grind
example (a : R) (_ : 3 ≤ a) : 9 ≤ a^2 := by grind
example (a b : R) (_ : 0 ≤ a) (_ : a ≤ b) : a^2 ≤ b^2 := by grind
example (a b : R) (_ : 0 ≤ a^3) (_ : 0 ≤ a * b) (_ : 0 ≤ b^3) : 0 ≤ a^5 * b^5 := by grind
