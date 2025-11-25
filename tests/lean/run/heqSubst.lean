example (f : α → α) (a b : α) (h : a ≍ b) : f a = f b := by
  subst h
  rfl
