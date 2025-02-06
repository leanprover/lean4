example (b : Bool) : (if (if b then true else true) then 1 else 2) = 1 := by
  split
  next h =>
    guard_target =ₛ (if true = true then 1 else 2) = 1
    guard_hyp h : b = true
    simp
  next h =>
    guard_target =ₛ (if true = true then 1 else 2) = 1
    guard_hyp h : ¬b = true
    simp
