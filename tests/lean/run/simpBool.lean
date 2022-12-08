example (h : x ≠ true) : (x && y) = false := by
  simp [h]

example (h : ¬ (x = true)) : (x && y) = false := by
  simp [h]

example (h : x ≠ false) : (x && y) = y := by
  simp [h]

example (h : ¬ (x = false)) : (x && y) = y := by
  simp [h]
