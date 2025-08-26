/--
info: Try this:
  simp only [Nat.reduceMul, a]
-/
#guard_msgs in
example : True := by
  let a := 10
  have : a * 2 = 10 * 2 := by
    simp [a]
  have : a * 2 = 10 * 2 := by
    simp? [a] -- should say simp only [Nat.reduceMul, a]
  trivial
