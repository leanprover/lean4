inductive bv : nat → Type
| nil  : bv 0
| cons : Π n, bool → bv n → bv (n+1)

open bv

definition f : ∀ n : nat, bv n → nat → nat
| (n+1) (cons .(n) b v) 1000000 := f n v 0
| (n+1) (cons .(n) b v) x       := f n v (x + 1)
| _     _                _      := 1

set_option pp.binder_types true

#check @f._main.equations._eqn_1
#check @f._main.equations._eqn_2
#check @f._main.equations._eqn_3

example (n : nat) (b : bool) (v : bv n) (x : nat) : x ≠ 1000000 → f (n+1) (cons n b v) x = f n v (x + 1) :=
assume H, f.equations._eqn_3 n b v x H
