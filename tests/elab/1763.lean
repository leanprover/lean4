axiom P : Prop → Prop

@[congr]
axiom P_congr (a b : Prop) (h : a ↔ b) : P a ↔ P b

theorem ex1 {p q : Prop} (h : p ↔ q) (h' : P q) : P p := by
  simp [h]
  assumption

#print ex1

theorem ex2 {p q : Prop} (h : p = q) (h' : P q) : P p := by
  simp [h]
  assumption

#print ex2
