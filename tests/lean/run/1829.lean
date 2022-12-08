theorem eq_iff_true_of_subsingleton [Subsingleton α] (x y : α) : x = y ↔ True :=
  ⟨fun _ => ⟨⟩, fun _ => (Subsingleton.elim ..)⟩

attribute [simp] eq_iff_true_of_subsingleton in
example : True := trivial

structure Func' (α : Sort _) (β : Sort _) :=
(toFun    : α → β)

def r : Func' α α := ⟨id⟩

@[simp] theorem r_toFun {α : Sort u_1} (a : α) : Func'.toFun r a = id a := rfl

example (x y : α) (h : x = y) : r.toFun x = y := by simp <;> rw [h]

theorem noissue (x y : α) (h : x = y) : r.toFun x = y := by simp <;> rw [h]
