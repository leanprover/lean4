set_option trace.blast true

example (p q : Prop) : p ∨ q → q ∨ p :=
by blast

definition lemma1 (p q r s : Prop) (a b : nat) : r ∨ s → p ∨ q → a = b → q ∨ p :=
by blast

print lemma1
