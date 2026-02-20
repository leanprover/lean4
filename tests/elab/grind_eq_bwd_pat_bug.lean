module
@[grind ←=] theorem inv_eq {α : Type} [One α] [Mul α] [Inv α] {a b : α} (w : a * b = 1) : a⁻¹ = b := sorry

theorem test {α : Type} [One α] [Mul α] [Inv α] {a b : α} (w : a * b = 1) : a⁻¹ = b := by
  grind
