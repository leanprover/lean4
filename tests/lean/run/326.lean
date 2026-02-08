class Monoid (α : Type u) [Zero α] extends Add α where
  zero_add (a : α) : 0 + a = a
  add_zero (a : α) : a + 0 = a

attribute [simp] Monoid.zero_add Monoid.add_zero

variable {α : Type u} [Zero α] [Monoid α]

-- works
example (a : α) : 0 + a = a := by simp

example (a : α) : a + 0 = a := by simp
