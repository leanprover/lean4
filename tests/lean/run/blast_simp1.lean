example (a b c : Prop) : a ∧ b ∧ c ↔ c ∧ b ∧ a :=
by blast

example (a b c : Prop) : a ∧ false ∧ c ↔ false :=
by blast

example (a b c : Prop) : a ∨ false ∨ b ↔ b ∨ a :=
by blast

example (a b c : Prop) : ¬ true ∨ false ∨ b ↔ b :=
by blast

example (a b c : Prop) : if true then a else b ↔ if false then b else a :=
by blast

example (a b : Prop) : a ∧ not a ↔ false :=
by blast
