attribute iff [reducible]
set_option blast.subst false
set_option blast.simp  false

definition lemma1 (p : nat → Prop) (a b c : nat) : p a → a = b → p b :=
by blast

set_option pp.beta true
print lemma1
