set_option debug.byAsSorry true in
/--
warning: declaration uses 'sorry'
-/
#guard_msgs in
theorem ex1 (h : b = a) : a = b := by
  rw [h]

/--
-/
#guard_msgs in
theorem ex2 (h : b = a) : a = b := by
  rw [h]
