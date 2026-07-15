/-!
Test for a bug at `registerNonlinearOccsAt`.
-/

example {a : Nat} (ha : 1 ≤ a) (H : a ^ 2 = 2 ^ a) : a = 1 ∨ a = 2 ∨ 3 ≤ a := by
  grind

example {a : Nat} (ha : 1 ≤ a) (H : a ^ 2 = 2 ^ a) : a = 1 ∨ 2 ≤ a := by grind

example {a : Nat} (ha : 2 ≤ a) (H : a ^ 2 = 2 ^ a) : a = 2 ∨ 3 ≤ a := by grind

example {a : Nat} (ha : 1 ≤ a) (_ : a ≤ 2) (_ : ¬ a = 1) (_ : ¬ a = 2) (H : a ^ 2 = 2 ^ a) : False := by
  grind

example {a : Nat} (ha : 1 ≤ a) : a = 1 ∨ a = 2 ∨ 3 ≤ a := by grind
