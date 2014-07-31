import logic

inductive nat : Type :=
| zero : nat
| succ : nat → nat

definition add (x y : nat) : nat := nat_rec x (λn r, succ r) y
infixl `+`:65 := add

axiom add_right_comm (n m k : nat) : n + m + k = n + k + m

print "==========================="
theorem bug (a b c d : nat) : a + b + c + d = a + c + b + d
:= subst (add_right_comm _ _ _) (refl (a + b + c + d))

