import logic
open eq.ops
namespace experiment
inductive nat : Type :=
| zero : nat
| succ : nat → nat

namespace nat
definition add (x y : nat) : nat := nat.rec x (λn r, succ r) y
infixl `+` := add
definition mul (n m : nat) := nat.rec zero (fun m x, x + n) m
infixl `*` := mul

axiom mul_zero_right (n : nat) : n * zero = zero

constant P : nat → Prop

print "==========================="
theorem tst (n : nat) (H : P (n * zero)) : P zero
:= eq.subst (mul_zero_right _) H
end nat
exit
