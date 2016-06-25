import data.list
open list tactic option
constants (A : Type.{1}) (x y z : A) (Hy : x = y) (Hz : y = z)
constants (f₁ : A → A) (f₂ : A → A → A)

meta_definition simp_x_to_y : tactic unit := mk_eq_simp_ext $
  (λ e:expr, do res ← mk_const "y",
                pf ← mk_const "Hy",
                return $ prod.mk res pf)

meta_definition simp_y_to_z : tactic unit := mk_eq_simp_ext $
  (λ e:expr, do res ← mk_const "z",
                pf ← mk_const "Hz",
                return $ prod.mk res pf)

register_simp_ext x simp_x_to_y
register_simp_ext y simp_y_to_z

print [simp_ext]

example : x = z := by simp >> triv
example : f₁ x = f₁ y := by simp >> triv
example : f₁ (f₂ x y) = f₁ (f₂ z z) := by simp >> triv
example : f₁ (f₂ x y) = f₁ (f₂ y x) := by simp >> triv
