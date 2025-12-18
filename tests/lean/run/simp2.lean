def p (x : Prop) := x

@[simp] theorem lemma1 (x : Prop) : p x = x :=
 rfl

theorem ex1 (x : Prop) (h : x) : p x := by
  simp +implicitDefEqProofs
  assumption

/--
info: theorem ex1 : ∀ (x : Prop), x → p x :=
fun x h => id h
-/
#guard_msgs in
#print ex1

theorem ex1' (x : Prop) (h : x) : p x := by
  simp -implicitDefEqProofs
  assumption

/--
info: theorem ex1' : ∀ (x : Prop), x → p x :=
fun x h => Eq.mpr (id (lemma1 x)) h
-/
#guard_msgs in
#print ex1'

theorem ex2 (x : Prop) (q : Prop → Prop) (h₁ : x) (h₂ : q x = x) : q x := by
  simp [h₂]
  assumption

/--
info: theorem ex2 : ∀ (x : Prop) (q : Prop → Prop), x → q x = x → q x :=
fun x q h₁ h₂ => Eq.mpr (id h₂) h₁
-/
#guard_msgs in
#print ex2
