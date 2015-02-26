import logic
namespace experiment
inductive nat : Type :=
| zero : nat
| succ : nat → nat

namespace nat
definition add (x y : nat) : nat := nat.rec x (λn r, succ r) y
infixl `+` := add

axiom add_right_comm (n m k : nat) : n + m + k = n + k + m
open eq
print "==========================="
theorem bug (a b c d : nat) : a + b + c + d = a + c + b + d
:= subst (add_right_comm _ _ _) (eq.refl (a + b + c + d))
end nat
end experiment
