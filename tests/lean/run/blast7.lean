set_option blast.strategy "preprocess"

lemma lemma1 (p : Prop) (a b : nat) : a = b → p → p :=
by blast

reveal lemma1
print lemma1
