example (q : p → Prop) (h : p = True)
  (h' : ∀(q : True → Prop), (∀ x, q x) ↔ q True.intro) :
    (∀ h', q h') ↔ q (h.symm ▸ trivial) := by
  simp only [h, h']

theorem forall_true_left : ∀ (p : True → Prop), (∀ (x : True), p x) ↔ p True.intro := sorry

example (p : Prop) (q : p → Prop) (h : p) :
  (∀ (h2 : p), q h2) ↔ q h :=
by simp only [h, forall_true_left]
