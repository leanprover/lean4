attribute iff [reducible]
set_option blast.strategy "ematch"

definition lemma1 (p : nat → Prop) (a b c : nat) : p a → a = b → p b :=
by blast

set_option pp.beta true
print lemma1
