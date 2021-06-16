example (p : Prop) [Decidable p] (hnp : ¬ p) :
    if decide p then 0 = 1 else 1 = 1 := by
  simp [hnp, decideEqFalse Unit]
