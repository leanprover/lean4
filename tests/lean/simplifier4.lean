/- Basic rewriting with a custom relation without congruence or conditionals -/
import logic.connectives data.nat

universe l
constant T : Type.{l}
constants (x y z : T) (f g h : T → T)
constants (R : T → T → Prop)
constants (R_refl : ∀ x, R x x) (R_sym : ∀ x y, R x y →  R y x) (R_trans : ∀ x y z, R x y → R y z → R x z)
constants (Hfxgy : R (f x) (g y)) (Hgyhz : R (g y) (h z))

attribute R_refl [refl]
attribute R_sym [symm]
#simplify R env 2 (f x) -- f x
attribute R_trans [trans]
#simplify R env 2 (f x) -- f x
attribute Hfxgy [simp]
#simplify R env 2 (f x) -- f x
attribute Hgyhz [simp]
#simplify R env 2 (f x) -- f x
