example : ∃ n : Nat, n = n := by
  refine ⟨?n, ?h⟩
  case h => exact Eq.refl 3
