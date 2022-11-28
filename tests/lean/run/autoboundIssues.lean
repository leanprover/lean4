example : n.succ = 1 → n = 0 := by
  intros h; injection h

example (h : n.succ = 1) : n = 0 := by
  injection h

opaque T : Type
opaque T.Pred : T → T → Prop

example {ρ} (hρ : ρ.Pred σ) : T.Pred ρ ρ := sorry
