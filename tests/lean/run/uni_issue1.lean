import logic
namespace experiment
inductive nat : Type :=
| zero : nat
| succ : nat → nat

definition is_zero (n : nat)
:= nat.rec true (λ n r, false) n
end experiment
