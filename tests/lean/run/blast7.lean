set_option blast.init_depth 10

lemma lemma1 (p : Prop) (a b : nat) : a = b → p → p :=
by blast

reveal lemma1
print lemma1
