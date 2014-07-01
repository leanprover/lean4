variable A : Type.{1}
definition bool [inline] : Type.{1} := Type.{0}
variable eq : A → A → bool
infixl `=`:50 := eq
axiom subst (P : A → bool) (a b : A) (H1 : a = b) (H2 : P a) : P b
axiom eq_trans (a b c : A) (H1 : a = b) (H2 : b = c) : a = c
axiom eq_refl (a : A) : a = a
variable le : A → A → bool
infixl `≤`:50 := le
axiom le_trans (a b c : A) (H1 : a ≤ b) (H2 : b ≤ c) : a ≤ c
axiom le_refl (a : A) : a ≤ a
axiom eq_le_trans (a b c : A) (H1 : a = b) (H2 : b ≤ c) : a ≤ c
axiom le_eq_trans (a b c : A) (H1 : a ≤ b) (H2 : b = c) : a ≤ c
calc_subst subst
calc_refl  eq_refl
calc_refl  le_refl
calc_trans eq_trans
calc_trans le_trans
calc_trans eq_le_trans
calc_trans le_eq_trans
variables a b c d e f : A
axiom H1 : a = b
axiom H2 : b ≤ c
axiom H3 : c ≤ d
axiom H4 : d = e
check calc a   = b : H1
           ... ≤ c : H2
           ... ≤ d : H3
           ... = e : H4

variable lt : A → A → bool
infixl `<`:50 := lt
axiom lt_trans (a b c : A) (H1 : a < b) (H2 : b < c) : a < c
axiom le_lt_trans (a b c : A) (H1 : a ≤ b) (H2 : b < c) : a < c
axiom lt_le_trans (a b c : A) (H1 : a < b) (H2 : b ≤ c) : a < c
axiom H5 : c < d
check calc b  ≤ c : H2
          ... < d : H5 -- Error le_lt_trans was not registered yet
calc_trans le_lt_trans
check calc b  ≤ c : H2
          ... < d : H5

variable le2 : A → A → bool
infixl `≤`:50 := le2
variable le2_trans (a b c : A) (H1 : le2 a b) (H2 : le2 b c) : le2 a c
calc_trans le2_trans
print raw calc b   ≤ c : H2
               ... ≤ d : H3
               ... ≤ e : H4
