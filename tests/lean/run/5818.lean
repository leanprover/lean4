theorem better2 : (UInt64.ofNat (2^64-1))%(2^63 : Nat) = 9223372036854775807 := by decide
theorem better1 : (UInt64.ofNat (2^64-1))%(2^63 : Nat) = 9223372036854775807 := by native_decide
