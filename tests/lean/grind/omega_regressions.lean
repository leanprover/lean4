-- These are test cases extracted from Mathlib, where `omega` works but `grind` does not (yet!)

example (n : Int) (n0 : ¬0 ≤ n) (a : Nat) : n ≠ (a : Int) := by grind
