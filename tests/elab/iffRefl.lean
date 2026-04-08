macro_rules | `(tactic| rfl) => `(tactic| exact Iff.rfl)

theorem r (A : Prop) : A ↔ A := by rfl

theorem s (A B : Prop) (h : A ↔ B) : B ↔ A := by
  rw [h]
