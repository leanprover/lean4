import logic
open tactic

inductive nat : Type :=
zero : nat,
succ : nat → nat

namespace nat
definition add [inline] (a b : nat) : nat
:= nat.rec a (λ n r, succ r) b
infixl `+`:65 := add

definition one [inline] := succ zero

-- Define coercion from num -> nat
-- By default the parser converts numerals into a binary representation num
definition pos_num_to_nat [inline] (n : pos_num) : nat
:= pos_num.rec one (λ n r, r + r) (λ n r, r + r + one) n
definition num_to_nat [inline] (n : num) : nat
:= num.rec zero (λ n, pos_num_to_nat n) n
coercion num_to_nat

-- Now we can write 2 + 3, the coercion will be applied
check 2 + 3

-- Define an assump as an alias for the eassumption tactic
definition assump : tactic := eassumption

theorem T1 {p : nat → Prop} {a : nat } (H : p (a+2)) : ∃ x, p (succ x)
:= by apply exists_intro; assump

definition is_zero (n : nat)
:= nat.rec true (λ n r, false) n

theorem T2 : ∃ a, (is_zero a) = true
:= by apply exists_intro; apply eq.refl

end nat
