constant P : nat → Prop
definition h [reducible] (n : nat) := n
definition foo [forward] : ∀ x, P (h x) := sorry

set_option blast.strategy "ematch"

example (n : nat) : P (h n) :=
by blast
