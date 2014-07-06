import standard

inductive nat : Type :=
| zero : nat
| succ : nat → nat

definition is_zero (n : nat)
:= nat_rec true (λ n r, false) n
