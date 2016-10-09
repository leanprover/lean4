open nat

set_option pp.binder_types true

inductive bv : nat → Type
| nil  : bv 0
| cons : ∀ (n) (hd : bool) (tl : bv n), bv (succ n)

open bv

variable (f : bool → bool → bool)

definition map2 : ∀ {n}, bv n → bv n → bv n
| 0     nil            nil             := nil
| (n+1) (cons .n b1 v1) (cons .n b2 v2) := cons n (f b1 b2) (map2 v1 v2)

check map2._main.equations.eqn_2

/- defining function again without simplifying the type of automatically generated lemmas -/

definition map2' : ∀ {n}, bv n → bv n → bv n
| 0     nil            nil             := nil
| (n+1) (cons .n b1 v1) (cons .n b2 v2) := cons n (f b1 b2) (map2' v1 v2)

check map2'._main.equations.eqn_2
