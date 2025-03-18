example : True := by
  let a := 1
  let b := 2
  have : b = 2 := by simp [a,b]
  have : a = 1 := by simp? [a]
  have : 1 = 1 := by simp?
  trivial

example : False := by
  let a := 1
  let b := 1
  have : a = 1 → False := sorry
  simp (disch := simp [b]) [this, a]
