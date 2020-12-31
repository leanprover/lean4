def p (x : Prop) := x

@[simp] theorem lemma1 (x : Prop) : p x = x :=
 rfl

theorem ex1 (x : Prop) (h : x) : p x := by
  simp
  assumption

#print ex1

theorem ex2 (x : Prop) (q : Prop → Prop) (h₁ : x) (h₂ : q x = x) : q x := by
  simp [h₂]
  assumption

#print ex2
