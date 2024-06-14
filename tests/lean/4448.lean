import Lean

@[deprecated]
theorem hi : True := .intro

example : True := by
  simp [hi, hi]
