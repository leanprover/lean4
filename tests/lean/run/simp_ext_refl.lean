open tactic

constants (A : Type.{1}) (x y z : A) (g : A → A) (Hg : g y = z)
attribute [simp] Hg

noncomputable definition f (a : A) := y
lemma f.def : ∀ (a), f a = y := λ a, rfl

meta definition simp_f_to_y : tactic unit := mk_eq_simp_ext $
  λ e, if expr.get_app_num_args e = 1
       then do res ← mk_const `y,
               pf ← mk_app `rfl [e],
               return (res, pf)
       else fail "expected f applied to one arg"

meta definition simp_f_to_y₂ : tactic unit := mk_eq_simp_ext $
  λ e, if expr.get_app_num_args e = 1
       then do res ← mk_const `y,
               pf ← mk_app `f.def [expr.app_arg e],
               return (res, pf)
       else fail "expected f applied to one arg"

register_simp_ext f simp_f_to_y

definition foo : g (f x) = z := by simp

register_simp_ext f simp_f_to_y₂

definition foo₂ : g (f x) = z := by simp

print foo
print foo₂
