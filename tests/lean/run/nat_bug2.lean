import logic
open num eq_ops

inductive nat : Type :=
zero : nat,
succ : nat → nat

abbreviation plus (x y : nat) : nat
:= nat_rec x (λn r, succ r) y
definition to_nat [coercion] [inline] (n : num) : nat
:= num_rec zero (λn, pos_num_rec (succ zero) (λn r, plus r (plus r (succ zero))) (λn r, plus r r) n) n
definition add (x y : nat) : nat
:= plus x y
variable le : nat → nat → Prop

infixl `+`:65 := add
infix `≤`:50  := le
axiom add_one (n:nat) : n + (succ zero) = succ n
axiom add_le_right {n m : nat} (H : n ≤ m) (k : nat) : n + k ≤ m + k

theorem succ_le {n m : nat} (H : n ≤ m) : succ n ≤ succ m
:= add_one m ▸ add_one n ▸ add_le_right H 1
