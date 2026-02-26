theorem ex (p q r : Prop) (h : p ∧ q ∧ r) : (¬q ∨ r) ∧ (¬r ∨ q) ∧ p := by
  simp [h]

#print ex
