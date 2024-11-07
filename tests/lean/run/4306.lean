/--
info: 12776324570088369205
-/
#guard_msgs in
#eval (123456789012345678901).toUInt64

/--
info: 12776324570088369205
-/
#guard_msgs in
#eval (123456789012345678901).toUInt64.toNat

/--
error: tactic 'native_decide' evaluated that the proposition
  (Nat.toUInt64 123456789012345678901).toNat = 123456789012345678901
is false
-/
#guard_msgs in
theorem false : False := by
  have : (123456789012345678901).toUInt64.toNat = 123456789012345678901 := by native_decide
  simp [Nat.toUInt64] at this
