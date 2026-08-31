/-
The following example requires the normalization rule `one_mul`
-/

theorem inv_lt_of_inv_lt₀ {a b : Rat} : 0 < a → a⁻¹ < b → b⁻¹ < a := sorry

example (ε : Rat) (hε : 0 < ε) (N : Rat) (hN : 1 / ε < N) (n : Rat) (hn : N ≤ n) : 1 / n < ε := by
  grind [inv_lt_of_inv_lt₀]
