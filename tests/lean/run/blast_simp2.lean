definition tst1 (a b : Prop) : a ∧ b ∧ true → b ∧ a :=
by simp

print tst1
