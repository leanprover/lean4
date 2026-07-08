variable (x : Id Nat) (h : x = x)

theorem Id_def : Id α = α := rfl

theorem bar : x = x.succ := by
  rw [Id_def] at x
  -- rw should not expose the auxdecl `bar`:
  fail_if_success assumption
  sorry
