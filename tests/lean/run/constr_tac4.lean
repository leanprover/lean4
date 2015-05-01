import data.nat

open nat

definition lt.trans {a b c : nat} (H₁ : a < b) (H₂ : b < c) : a < c :=
have aux : a < b → a < c, from
  lt.rec_on H₂
    (λ h₁, lt.step h₁)
    (λ b₁ bb₁ ih h₁, by constructor; exact ih h₁),
aux H₁

definition succ_lt_succ {a b : nat} (H : a < b) : succ a < succ b :=
lt.rec_on H
  (by constructor)
  (λ b hlt ih, lt.trans ih (by constructor))

definition lt_of_succ_lt {a b : nat} (H : succ a < b) : a < b :=
lt.rec_on H
  (by constructor; constructor)
  (λ b h ih, by constructor; exact ih)
