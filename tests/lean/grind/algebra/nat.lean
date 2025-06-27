
open Lean.Grind

variable [CommRing R] [LinearOrder R] [OrderedRing R]
example (a b : R) (h : 0 ≤ a * b) : 0 ≤ b * a := by grind
example (a b : R) (h : 7 ≤ a * b) : 7 ≤ b * a := by grind

-- These don't work because `cutsat` disables `linarith`.
-- We could use the CommRing normalizer in cutsat to solve these.
example (a b : Int) (h : 0 ≤ a * b) : 0 ≤ b * a := by grind
example (a b : Int) (h : 7 ≤ a * b) : 7 ≤ b * a := by grind

-- These should work by embedding `Nat` into its Grothendieck completion,
-- and using that the embedding is monotone.
example (a b : Nat) (h : 0 ≤ a * b) : 0 ≤ b * a := by grind
example (a b : Nat) (h : 7 ≤ a * b) : 7 ≤ b * a := by grind
