variable A : Type.{1}
definition [inline] bool : Type.{1} := Type.{0}
variable eq : A → A → bool
infixl `=` 50 := eq
variable subst (P : A → bool) (a b : A) (H1 : a = b) (H2 : P a) : P b
variable eq_trans (a b c : A) (H1 : a = b) (H2 : b = c) : a = c
variable eq_refl (a : A) : a = a
variable le : A → A → bool
infixl `≤` 50 := le
variable le_trans (a b c : A) (H1 : a ≤ b) (H2 : b ≤ c) : a ≤ c
variable le_refl (a : A) : a ≤ a
variable eq_le_trans (a b c : A) (H1 : a = b) (H2 : b ≤ c) : a ≤ c
calc_subst subst
calc_refl  eq_refl
calc_refl  le_refl
calc_trans eq_trans
calc_trans le_trans
calc_trans eq_le_trans
