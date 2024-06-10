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
error: application type mismatch
  Lean.ofReduceBool false._nativeDecide_1 true (Eq.refl true)
argument has type
  true = true
but function has type
  Lean.reduceBool false._nativeDecide_1 = true → false._nativeDecide_1 = true
-/
#guard_msgs in
theorem false : False := by
  have : (123456789012345678901).toUInt64.toNat = 123456789012345678901 := by native_decide
  simp [Nat.toUInt64] at this
