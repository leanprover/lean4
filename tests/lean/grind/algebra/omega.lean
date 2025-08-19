-- From Mathlib.Algebra.Order.Group.Unbundled.Int

-- From Mathlib.Order.RelSeries
theorem RelSeries.inductionOn.extracted_3 (p : Nat) (heq : p = 0) (n : Fin (p + 1)) : n = 0 := by
  grind

theorem LTSeries.length_lt_card.extracted_1 (s : Nat)
  (i j : Fin (s + 1)) (hn : i ≠ j) (hl : ¬i < j) : j < i := by
  grind

-- From Mathlib.AlgebraicTopology.SimplexCategory.Basic
theorem SimplexCategory.mkOfLe_refl.extracted_1 {n : Nat} (j : Fin (n + 1)) : j ≤ j := by
  grind

theorem SimplexCategory.eq_σ_comp_of_not_injective.extracted_1 {n : Nat}
  (x y : Fin ((n + 1) + 1)) (h₂ : ¬x = y) (h : ¬x < y) :
  y < x := by
  fail_if_success grind
  omega
