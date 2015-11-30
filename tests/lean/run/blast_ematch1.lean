import data.nat
open nat
constant f : nat → nat
constant g : nat → nat

definition lemma1 [forward] : ∀ x, (:g (f x):) = x :=
sorry

set_option blast.init_depth 10
set_option blast.inc_depth 1000
set_option blast.subst false
set_option blast.ematch true

example (a b c : nat) : a = f b → a = f c → g a ≠ b → false :=
by blast
