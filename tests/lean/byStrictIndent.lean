theorem byNestedStrictIndent (n : Nat) (h : n > 0) : n > 1 := by
  have helper : n > 1 := by
  sorry -- expected '{' or strict indentation
  sorry

--
theorem byNestedBad₁ (n : Nat) (h : n > 0) : n > 1 := by
  have helper : n > 1 := by
    sorry
   sorry -- expected command
  sorry

theorem byNestedBad₂ (n : Nat) (h : n > 0) : n > 1 := by
  have helper : n > 1 := by
    sorry
      sorry -- expected command
  sorry
