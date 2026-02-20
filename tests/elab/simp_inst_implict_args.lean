/-
This test ensures `simp` will not try to synthesize instance implicit arguments when they can
be inferred by unification. Note that in some cases the inferred instance may not even be
definitionally equal to the inferred one, and would prevent the [simp] theorem from being applied.
-/
theorem dec_and (p q : Prop) [Decidable (p ∧ q)] [Decidable p] [Decidable q] : decide (p ∧ q) = (p && q) := by
  by_cases p <;> by_cases q <;> simp [*]

theorem dec_not (p : Prop) [Decidable (¬p)] [Decidable p] : decide (¬p) = !p := by
  by_cases p <;> simp [*]

example [Decidable u] [Decidable v] : decide (u ∧ (v → False)) = (decide u && !decide v) := by
  simp only [imp_false]
  simp only [dec_and]
  simp only [dec_not]
