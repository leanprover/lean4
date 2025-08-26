/--
info: Try this:
  simp only [ha, Nat.reduceEqDiff, imp_self]
-/
#guard_msgs in
theorem foo₁ (a : Nat) (ha : a = 37) :
    (match h : a with | 42 => by simp_all | n => n) = 37 := by
  simp? [ha]

theorem foo₂ (a : Nat) (ha : a = 37) (hb : b = 37)  :
    (match h : a with | 42 => by simp_all | n => n) = b := by
  simp only [ha, Nat.reduceEqDiff, imp_self]
  guard_target =ₛ 37 = b
  rw [hb]
