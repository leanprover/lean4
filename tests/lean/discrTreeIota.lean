@[simp] theorem liftOn_mk (a : α) (f : α → γ) (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) :
    Quot.liftOn (Quot.mk r a) f h = f a := rfl

theorem eq_iff_true_of_subsingleton [Subsingleton α] (x y : α) : x = y ↔ True :=
  iff_true _ ▸ Subsingleton.elim ..

section attribute [simp] eq_iff_true_of_subsingleton end

@[simp] theorem PUnit.default_eq_unit : (default : PUnit) = PUnit.unit := rfl

set_option trace.Meta.Tactic.simp.discharge true
set_option trace.Meta.Tactic.simp.unify true
set_option trace.Meta.Tactic.simp.rewrite true
example : (default : PUnit) = x := by simp
