-- These are test cases extracted from Mathlib, where `omega` works but `grind` does not (yet!)

example (n : Int) (n0 : ¬0 ≤ n) (a : Nat) : n ≠ (a : Int) := by grind

-- TODO: add to the library?
attribute [grind] Int.negSucc_eq

example (p : Int) (n : Nat) (hmp : Int.negSucc (n + 1) + 1 = p)
  (hnm : Int.negSucc (n + 1 + 1) + 1 = Int.negSucc (n + 1)) : p = Int.negSucc n := by grind
