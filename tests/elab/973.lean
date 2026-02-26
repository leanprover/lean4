universe u
variable {α : Sort u} {p : α → Prop}

@[simp]
theorem Subtype.coe_mk  (x : α) (h : p x) : (Subtype.mk x h).val = x :=
 rfl

example (x : Nat) (h : x > 0) : (Subtype.mk x h).val = x := by
  simp

set_option trace.Meta.Tactic.simp.discharge true
example : True := by simp
