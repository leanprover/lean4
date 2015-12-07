set_option blast.strategy "preprocess"

example (p q r : Prop) (a b : nat) : true → a = a → q → q → p → p :=
by blast
