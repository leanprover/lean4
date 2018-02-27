def f := @id
@[simp] lemma foo {α : Type} [inhabited α] : f = @id α := rfl

example : f = @id ℕ := by simp
