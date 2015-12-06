set_option blast.strategy "preprocess"

lemma T1 (a b : Prop) : false → a :=
by blast

reveal T1
print T1

lemma T2 (a b c : Prop) : ¬ a → b → a → c :=
by blast

reveal T2
print T2

example (a b c : Prop) : a → b → ¬ a → c :=
by blast

example (a b c : Prop) : a → b → b → ¬ a → c :=
by blast
