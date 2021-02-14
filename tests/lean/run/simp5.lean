def f {α} (a b : α) := a

theorem f_Eq {α} (a b : α) : f a b = a :=
  rfl

theorem ex (a b c : α) : f (f a b) c = a := by
  simp [f_Eq]

#print ex
