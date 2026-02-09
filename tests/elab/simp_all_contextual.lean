theorem ex (h : a = 0) (p : Nat → Prop) : p a → p 0 := by
  simp_all
