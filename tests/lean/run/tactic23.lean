import logic
namespace experiment
inductive nat : Type :=
| zero : nat
| succ : nat → nat

namespace nat
definition add (a b : nat) : nat
:= nat.rec a (λ n r, succ r) b
infixl `+` := add

definition one := succ zero

-- Define coercion from num -> nat
-- By default the parser converts numerals into a binary representation num
definition pos_num_to_nat (n : pos_num) : nat
:= pos_num.rec one (λ n r, r + r) (λ n r, r + r + one) n
definition num_to_nat (n : num) : nat
:= num.rec zero (λ n, pos_num_to_nat n) n
attribute num_to_nat [coercion]

check (2:num) + 3

-- Define an assump as an alias for the eassumption tactic
definition assump : tactic := tactic.eassumption

theorem T1 {p : nat → Prop} {a : nat } (H : p (a+(2:num))) : ∃ x, p (succ x)
:= by apply exists.intro; assump

definition is_zero (n : nat)
:= nat.rec true (λ n r, false) n

theorem T2 : ∃ a, (is_zero a) = true :=
by existsi zero; apply eq.refl

end nat
end experiment
