def f (a : α) := a

example (a b : α) (x y : β) : a ≍ x → x = y → y ≍ b → f a = f b := by
  grind

example (a b : α) (x y : β) : x = y → a ≍ x → y ≍ b → f a = f b := by
  grind
