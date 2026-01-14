/-!
This test guards against a constant folding bug
-/


def danger : UInt64 := UInt64.ofNat UInt64.size - 1
theorem danger_eq_large : danger = 18446744073709551615 := by decide +kernel
/--
error: Tactic `native_decide` evaluated that the proposition
  danger = 1
is false
-/
#guard_msgs in
theorem danger_eq_one : danger = 1 := by native_decide
theorem bad : False := by simpa using danger_eq_large.symm.trans danger_eq_one

def danger2 (x : Nat) : Nat := 0 - x
theorem danger2_eq_zero : danger2 1 = 0 := by decide +kernel
/--
error: Tactic `native_decide` evaluated that the proposition
  danger2 1 = 1
is false
-/
#guard_msgs in
theorem danger2_eq_one : danger2 1 = 1 := by native_decide
theorem bad2 : False := by simpa using danger2_eq_zero.symm.trans danger2_eq_one
