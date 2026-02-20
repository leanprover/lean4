example : if x = 0 then y + x = y else x ≠ 0 := by
  simp (config := { contextual := true })

example : if x = 0 then y + x = y else x ≠ 0 := by
  split
  simp_all
  simp_all

example : if x = 0 then y + x = y else x ≠ 0 := by
  simp (config := { contextual := true })
  split -- Error: no goals to be solved
