def f (a : α) := a

example (a b : α) (x y : β) : HEq a x → x = y → HEq y b → f a = f b := by
  grind

example (a b : α) (x y : β) : x = y → HEq a x → HEq y b → f a = f b := by
  grind
