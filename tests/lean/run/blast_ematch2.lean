import data.nat
open nat
constant f : nat → nat
constant g : nat → nat

definition lemma1 [forward] : ∀ x, g (f x) = x :=
sorry

set_option blast.strategy "ematch"

example (a b : nat) : f a = f b → a = b :=
by blast
