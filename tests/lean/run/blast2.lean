set_option blast.strategy "preprocess"

example (a b : Prop) : forall (Ha : a) (Hb : b), a :=
by blast

example (a b : Prop) : a → b → a :=
by blast
