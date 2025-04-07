reset_grind_attrs%

example [BEq α] (a b : α) : (a == b && a == b) = (a == b) := by
  rw [Bool.eq_iff_iff]
  grind -- succeeds

example [BEq α] (a b : α) : (a == b && a == b) = (a == b) := by
  grind -- fails
