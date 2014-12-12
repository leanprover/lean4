import data.list
open nat list

set_option pp.implicit true
set_option pp.notation false

definition filter {A : Type} (p : A → Prop) [H : decidable_pred p] : list A → list A,
filter nil      := nil,
filter (h :: t) := if p h then h :: filter t else filter t

open decidable

definition decidable_eq_nat : Π (a b : nat), decidable (a = b),
decidable_eq_nat 0 0         := inl rfl,
decidable_eq_nat 0 (x+1)     := inr (ne.symm (succ_ne_zero x)),
decidable_eq_nat (x+1) 0     := inr (succ_ne_zero x),
decidable_eq_nat (x+1) (y+1) :=
  decidable.cases_on (decidable_eq_nat x y)
    (λ Hp, inl (congr_arg succ Hp))
    (λ Hn, inr (λ H : x+1 = y+1, absurd (succ.inj H) Hn))

/-
match (decidable_eq_nat x y) with
  (inl Hp) := inl (congr_arg succ Hp),
  (inr Hn) := inr (λ Hs, absurd (succ.inj Hs) Hn)
-/
