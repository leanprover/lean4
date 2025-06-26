example (h : z = 9) : let x := 5; let y := 4; x + y = z := by
  intro x
  simp
  guard_target =ₛ x + 4 = z
  rw [h]

example (h : z = 9) : let x := 5; let y := 4; x + y = z := by
  intro x
  simp (config := { zetaDelta := true })
  guard_target =ₛ 9 = z
  rw [h]

example (h : z = 9) : let x := 5; let y := 4; x + y = z := by
  intro x
  simp [x]
  guard_target =ₛ 9 = z
  rw [h]

example (h : z = 9) : let x := 5; let y := 4; x + y = z := by
  intro x
  simp (config := { zetaDelta := true, zeta := false })
  guard_target =ₛ have y := 4; 5 + y = z
  rw [h]
