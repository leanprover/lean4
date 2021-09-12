example : (p → q → False) ↔ (¬ p ∨ ¬ q) := by
  apply Iff.intro
  . intro h
    byCases hp:p <;> byCases hq:q
    . specialize h hp hq; contradiction
    . exact Or.inr hq
    . exact Or.inl hp
    . exact Or.inr hq
  . intro
    | Or.inl hnp => intros; contradiction
    | Or.inr hnq => intros; contradiction
