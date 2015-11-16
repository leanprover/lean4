set_option blast.init_depth 10
set_option blast.inc_depth 1000

definition lemma1 (p q : Prop) : p ∧ q → q ∧ p :=
by blast

definition lemma2 (p q r s : Prop) : r ∧ s → p ∧ q → q ∧ p :=
by blast

print lemma2 -- unnecessary and.rec's are not included

example (p q : Prop) : p ∧ p ∧ q ∧ q → q ∧ p :=
by blast
