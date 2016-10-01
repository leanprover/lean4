open tactic

set_option simplify.theory false
set_option pp.implicit true

meta definition simplify_goal_force : tactic unit :=
do (new_target, Heq) ← target >>= simplify failed [],
   assert `Htarget new_target, swap,
   Ht ← get_local `Htarget,
   mk_app `eq.mpr [Heq, Ht] >>= apply_core transparency.all ff tt,
   try reflexivity

universe l

constants (f₁ : Π (X : Type*) (X_grp : group X), X)
constants (f₂ : Π (X : Type*) [X_grp : group X], X)
constants (A : Type l) (A_grp₁ : group A)

attribute [irreducible] noncomputable definition A_grp₂ : group A := A_grp₁
attribute [irreducible] noncomputable definition A_grp₃ (t : true) : group A := A_grp₁

set_option simplify.canonize_instances_fixed_point true
example : @f₂ A A_grp₁ = @f₂ A A_grp₂ := by simplify_goal_force
example : @f₂ A (A_grp₃ trivial) = @f₂ A A_grp₂ := by simplify_goal_force
example : @f₂ A (A_grp₃ trivial) = @f₂ A A_grp₂ := by simplify_goal_force
