open BitVec

example : (Fin.mk 5 (by decide) : Fin 10) + 2 = x := by
  simp
  guard_target =ₛ 7 = x
  sorry

example : (Fin.mk 5 (by decide) : Fin 10) + 2 = x := by
  simp (config := { ground := true }) only
  guard_target =ₛ 7 = x
  sorry

example : (BitVec.ofFin (Fin.mk 2 (by decide)) : BitVec 32) + 2 = x := by
  simp
  guard_target =ₛ 4#32 = x
  sorry

example : (BitVec.ofFin (Fin.mk 2 (by decide)) : BitVec 32) + 2 = x := by
  simp (config := { ground := true }) only
  guard_target =ₛ 4#32 = x
  sorry

example : (BitVec.ofFin 2 : BitVec 32) + 2 = x := by
  simp
  guard_target =ₛ 4#32 = x
  sorry

example (h : -2 = x) : Int.negSucc 3 + 2 = x := by
  simp
  guard_target =ₛ -2 = x
  assumption

example (h : -2 = x) : Int.negSucc 3 + 2 = x := by
  simp (config := { ground := true }) only
  guard_target =ₛ -2 = x
  assumption

example : Int.ofNat 3 + 2 = x := by
  simp
  guard_target =ₛ 5 = x
  sorry

example : Int.ofNat 3 + 2 = x := by
  simp (config := { ground := true }) only
  guard_target =ₛ 5 = x
  sorry

example (h : 5 = x) : UInt32.ofNat 2 + 3 = x := by
  simp
  guard_target =ₛ 5 = x
  assumption

example (h : 5 = x) : UInt32.ofNat 2 + 3 = x := by
  simp (config := { ground := true }) only
  guard_target =ₛ 5 = x
  assumption
