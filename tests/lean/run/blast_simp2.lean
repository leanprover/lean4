set_option blast.recursor false

definition tst1 (a b : Prop) : a ∧ b ∧ true → b ∧ a :=
by blast

print tst1
