set_option trace.blast true
set_option trace.blast.action false

example (a b : Prop) : a ∧ b → b ∧ a :=
by blast
