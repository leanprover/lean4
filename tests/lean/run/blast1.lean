set_option blast.strategy "preprocess"

example (a b : Prop) (Ha : a) (Hb : b) : a :=
by blast
