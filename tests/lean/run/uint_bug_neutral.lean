/-!
This test guards against a uint constant folding bug
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
