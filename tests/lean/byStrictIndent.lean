--

-- no indentation on top-level `by` is still allowed
theorem by_top_level_no_indent (n : Nat) (h : n > 1) : n > 1 := by
exact h

#print by_top_level_no_indent

--
theorem by_nested_strict_indent (n : Nat) (h : n > 0) : n > 1 := by
  have helper : n > 1 := by
  sorry -- expected '{' or strict indentation
  sorry

--
theorem by_nested_bad₁ (n : Nat) (h : n > 0) : n > 1 := by
  have helper : n > 1 := by
    sorry
   sorry -- expected command
  sorry

theorem by_nested_bad₂ (n : Nat) (h : n > 0) : n > 1 := by
  have helper : n > 1 := by
    sorry
      sorry -- expected command
  sorry
