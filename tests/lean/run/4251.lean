/--
info: Try this:
  [apply] simp only [ha, Nat.reduceEqDiff, imp_self]
-/
#guard_msgs in
example (a : Nat) (ha : a = 37) :
    (match (generalizing := false) h : a with | 42 => by simp_all | n => n) = 37 := by
  simp? [ha]

example (a : Nat) (ha : a = 37) (hb : b = 37)  :
    (match (generalizing := false) h : a with | 42 => by simp_all | n => n) = b := by
  simp only [ha, Nat.reduceEqDiff, imp_self]
  guard_target =ₛ 37 = b
  rw [hb]

/--
info: Try this:
  [apply] simp only [ha]
-/
#guard_msgs in
example (a : Nat) (ha : a = 37) :
    (match a with | 42 => by simp_all | n => n) = 37 := by
  simp? [ha]

example (a : Nat) (ha : a = 37) (hb : b = 37)  :
    (match a with | 42 => by simp_all | n => n) = b := by
  simp only [ha]
  guard_target =ₛ 37 = b
  rw [hb]
