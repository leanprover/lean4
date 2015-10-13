import logic
open eq.ops
namespace experiment
inductive nat : Type :=
| zero : nat
| succ : nat → nat

namespace nat
definition plus (x y : nat) : nat
:= nat.rec x (λn r, succ r) y
definition to_nat [coercion] (n : num) : nat
:= num.rec zero (λn, pos_num.rec (succ zero) (λn r, plus r (plus r (succ zero))) (λn r, plus r r) n) n
definition add (x y : nat) : nat
:= plus x y
constant le : nat → nat → Prop

infixl `+` := add
infix `≤`  := le
axiom add_one (n:nat) : n + (succ zero) = succ n
axiom add_le_right {n m : nat} (H : n ≤ m) (k : nat) : n + k ≤ m + k

theorem succ_le {n m : nat} (H : n ≤ m) : succ n ≤ succ m
:= add_one m ▸ add_one n ▸ add_le_right H (1:num)

end nat
end experiment
