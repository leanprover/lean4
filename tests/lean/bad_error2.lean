open nat

example {k n m : ℕ} (h : k + n ≤ k + m) : n ≤ m :=
match le.dest h with
| ⟨w, hw⟩ := @le.intro _ _ w
    begin
      -- hw is beta reduced after we added the equation compiler preprocessor.
      -- So, this test is not really relevant anymore.
      rw [nat.add_assoc] at hw,
      apply nat.add_left_cancel hw
    end
end
