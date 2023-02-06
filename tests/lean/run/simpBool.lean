example {x y : Bool} (h : ¬ x) : (x && y) = false := by
  simp [h]

example {x y : Bool} (h : x) : (x && y) = y := by
  simp [h]
