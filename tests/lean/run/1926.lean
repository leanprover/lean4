theorem forall_true_left : ∀ (p : True → Prop), (∀ (x : True), p x) ↔ p True.intro := sorry

theorem forall_prop_congr' {p p' : Prop} {q q' : p → Prop}
  (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') : (∀ h, q h) = ∀ h : p', q' (hp.2 h) :=
sorry

attribute [congr] forall_prop_congr'

example (p : Prop) (q : p → Prop) (h : p) :
  (∀ (h2 : p), q h2) ↔ q h :=
by simp only [h, forall_true_left]
