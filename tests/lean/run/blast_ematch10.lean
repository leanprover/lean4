attribute iff [reducible]

example (p : nat → Prop) (a b c : nat) : p a → a = b → p b :=
by blast
