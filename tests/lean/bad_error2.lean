open nat

example {k n m : ℕ} (h : k + n ≤ k + m) : n ≤ m :=
match le.dest h with
| ⟨w, hw⟩ := @le.intro _ _ w
    begin
      -- in the following error pp.beta is automatically disabled
      rw [nat.add_assoc] at hw,
      apply nat.add_left_cancel hw
    end
end
