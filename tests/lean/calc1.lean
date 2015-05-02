prelude constant A : Type.{1}
definition bool : Type.{1} := Type.{0}
constant eq : A → A → bool
infixl `=`:50 := eq
axiom subst (P : A → bool) (a b : A) (H1 : a = b) (H2 : P a) : P b
axiom eq_trans (a b c : A) (H1 : a = b) (H2 : b = c) : a = c
axiom eq_refl (a : A) : a = a
constant le : A → A → bool
infixl `≤`:50 := le
axiom le_trans (a b c : A) (H1 : a ≤ b) (H2 : b ≤ c) : a ≤ c
axiom le_refl (a : A) : a ≤ a
axiom eq_le_trans (a b c : A) (H1 : a = b) (H2 : b ≤ c) : a ≤ c
axiom le_eq_trans (a b c : A) (H1 : a ≤ b) (H2 : b = c) : a ≤ c
attribute subst [subst]
attribute eq_refl [refl]
attribute le_refl [refl]
attribute eq_trans [trans]
attribute le_trans [trans]
attribute eq_le_trans [trans]
attribute le_eq_trans [trans]
constants a b c d e f : A
axiom H1 : a = b
axiom H2 : b ≤ c
axiom H3 : c ≤ d
axiom H4 : d = e
check calc a   = b : H1
           ... ≤ c : H2
           ... ≤ d : H3
           ... = e : H4

constant lt : A → A → bool
infixl `<`:50 := lt
axiom lt_trans (a b c : A) (H1 : a < b) (H2 : b < c) : a < c
axiom le_lt_trans (a b c : A) (H1 : a ≤ b) (H2 : b < c) : a < c
axiom lt_le_trans (a b c : A) (H1 : a < b) (H2 : b ≤ c) : a < c
axiom H5 : c < d
check calc b  ≤ c : H2
          ... < d : H5 -- Error le_lt_trans was not registered yet
attribute le_lt_trans [trans]
check calc b  ≤ c : H2
          ... < d : H5

constant le2 : A → A → bool
infixl `≤`:50 := le2
constant le2_trans (a b c : A) (H1 : le2 a b) (H2 : le2 b c) : le2 a c
attribute le2_trans [trans]
print raw calc b   ≤ c : H2
               ... ≤ d : H3
               ... ≤ e : H4
