def foo : list ℕ := [2]
lemma bar : foo = foo := by dunfold foo
