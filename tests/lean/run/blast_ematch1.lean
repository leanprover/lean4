import data.nat
open nat
constant f : nat → nat
constant g : nat → nat

definition lemma1 [forward] : ∀ x, (:g (f x):) = x :=
sorry

set_option blast.strategy "ematch"

example (a b c : nat) : a = f b → a = f c → g a ≠ b → false :=
by blast
