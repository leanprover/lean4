definition f : nat → nat := sorry
definition g (a : nat) := f a
lemma gax [simp] : ∀ a, g a = 0 := sorry

attribute g [reducible]

example (a : nat) : f (a + a) = 0 :=
by simp
