example (f : α → α) (a b : α) (h : HEq a b) : f a = f b := by
  subst h
  rfl
