import standard
using num eq_ops

inductive nat : Type :=
| zero : nat
| succ : nat → nat

definition add (x y : nat) : nat := nat_rec x (λn r, succ r) y
infixl `+`:65 := add
definition mul (n m : nat) := nat_rec zero (fun m x, x + n) m
infixl `*`:75 := mul

axiom mul_succ_right (n m : nat) : n * succ m = n * m + n

theorem small2 (n m l : nat) : n * succ l + m = n * l + n + m
:= subst (mul_succ_right _ _) (refl (n * succ l + m))

