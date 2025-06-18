-- These are test cases extracted from Mathlib, where `ring` works but `grind` does not (yet!)
-- We need a semiring normalizer
example (a b : Nat) : 3 * a * b = a * b * 3 := by grind

example (k z : Nat) : k * (z * 2 * (z * 2 + 1)) = z * (k * (2 * (z * 2 + 1))) := by grind
