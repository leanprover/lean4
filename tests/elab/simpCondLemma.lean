@[simp] axiom divSelf (x : Nat) : x ≠ 0 → x/x = 1

theorem ex (x : Nat) (h : x ≠ 0) : (if x/x = 1 then 0 else 1) = 0 := by
  simp [h]
