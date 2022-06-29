example : n.succ = 1 → n = 0 := by
  intros h; injection h; assumption

example (h : n.succ = 1) : n = 0 := by
  injection h; assumption

opaque T : Type
opaque T.Pred : T → T → Prop

example {ρ} (hρ : ρ.Pred σ) : T.Pred ρ ρ := sorry
