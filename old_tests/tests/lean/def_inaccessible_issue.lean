open nat

set_option pp.binder_types true

inductive bv : nat → Type
| nil  : bv 0
| cons : ∀ (n) (hd : bool) (tl : bv n), bv (n+1)

open bv

variable (f : bool → bool → bool)

definition map2 : ∀ {n}, bv n → bv n → bv n
| 0     nil            nil             := nil
| (n+1) (cons .(n) b1 v1) (cons .(n) b2 v2) := cons n (f b1 b2) (map2 v1 v2)

#check map2.equations._eqn_2
