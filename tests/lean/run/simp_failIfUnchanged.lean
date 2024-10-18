example (h : False) : False := by
  fail_if_success
    simp (config := { failIfUnchanged := true })
  cases h

example (h : (a :: [b]).length = 3) : False := by
  fail_if_success
    simp (config := { failIfUnchanged := true }) only at h
  simp (config := { failIfUnchanged := false }) only at h
  simp (config := { failIfUnchanged := true }) at h

example (h : False) : False := by
  fail_if_success
    dsimp (config := { failIfUnchanged := true })
  cases h

example (_h : 37 = 37) (w : Inhabited False) : False ∨ False := by
  -- removes `_h` and simplifies the goal
  simp_all (config := { failIfUnchanged := true })
  -- Now should fail, because it can't do anything.
  fail_if_success
    simp_all (config := { failIfUnchanged := true })
  cases w with
  | mk w => cases w

example (h : False) : 7 = 8 := by
  simp (config := { failIfUnchanged := true })
  cases h
