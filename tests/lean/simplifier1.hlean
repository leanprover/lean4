open nat
-- deeper congruence

universe l
constants (T : Type.{l}) (x1 x2 x3 x4 x5 x6 : T) (f : T → T → T)
constants (f_comm : ∀ x y, f x y = f y x)
          (f_l : ∀ x y z, f (f x y) z = f x (f y z))
          (f_r : ∀ x y z, f x (f y z) = f y (f x z))
namespace tst
attribute f_comm [simp]
attribute f_l [simp]
attribute f_r [simp]
end tst
#simplify eq tst 0 (f (f x2 x4) (f x5 (f x3 (f x1 x6))))

open is_trunc

constants g : Π (x y : nat), x ≠ y → Type₁
constants a b c : nat
constants H₁ : a ≠ b
constants H₂ : a = c
namespace tst attribute H₂ [simp] end tst

definition ne_is_prop [instance] (a b : nat) : is_prop (a ≠ b) :=
sorry
-- TODO(Daniel): simplifier seems to have applied unnecessary step (see: (eq.nrec ... (eq.refl ..)))
#simplify eq tst 0 (g a b H₁)
