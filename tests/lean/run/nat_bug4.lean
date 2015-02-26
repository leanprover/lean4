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

axiom mul_succ_right (n m : nat) : n * succ m = n * m + n
open eq
theorem small2 (n m l : nat) : n * succ l + m = n * l + n + m
:= subst (mul_succ_right _ _) (eq.refl (n * succ l + m))
end nat
end experiment
