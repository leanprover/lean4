-- Basic (propositional) forward chaining with nested backward chaining
constants (A B C D : Prop)
set_option blast.trace true
set_option blast.init_depth 10
set_option blast.inc_depth 1000
set_option pp.all true

definition lemma1 : A → (A → B) → C → B ∧ C :=
by blast
