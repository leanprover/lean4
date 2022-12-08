example : ∃ n : Nat, n = n := by
  refine ⟨?n, ?h⟩
  case h => exact Eq.refl 3

example : ∃ n : Nat, n = n := by
  refine ⟨?n, ?h⟩
  case h => exact rfl
  case n => exact 3

example : ∃ n : Nat, n = n := by
  refine ⟨?n, by rfl⟩
  case n => exact 3

example : ∃ n : Nat, n = n := by
  refine ⟨?n, ?h⟩
  case h =>
    refine rfl
    case n => exact 3
