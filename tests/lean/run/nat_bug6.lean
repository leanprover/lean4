import standard
using eq_ops

inductive nat : Type :=
| zero : nat
| succ : nat → nat

definition add (x y : nat) : nat := nat_rec x (λn r, succ r) y
infixl `+`:65 := add
definition mul (n m : nat) := nat_rec zero (fun m x, x + n) m
infixl `*`:75 := mul

axiom mul_zero_right (n : nat) : n * zero = zero

variable P : nat → Prop

print "==========================="
theorem tst (n : nat) (H : P (n * zero)) : P zero
:= subst (mul_zero_right _) H
