def OrderDual (α : Type u) : Type u := α

variable (α : Type u) [LE α] {a b : α}
instance : LE (OrderDual α) := ⟨fun x y : α => y ≤ x⟩

theorem foo' (c : α) : a ≤ b := sorry

example : a ≤ b :=
  foo' (OrderDual α) a

theorem foo : a ≤ b := sorry

example : a ≤ b :=
  foo (OrderDual α)
