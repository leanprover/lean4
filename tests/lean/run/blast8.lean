open nat
set_option blast.strategy "preprocess"

lemma l1 (a : nat) : zero = succ a → a = a → false :=
by blast

lemma l2 (p : Prop) (a : nat) : zero = succ a → a = a → p :=
by blast

lemma l3 (a b : nat) : succ (succ a) = succ (succ b) → a = b :=
by blast

lemma l4 (a b : nat) : succ a = succ b → a = b :=
by blast

lemma l5 (a b c : nat) : succ (succ a) = succ (succ b) → c = c :=
by blast

reveal l3 l4 l5
print l3
print l4
print l5
