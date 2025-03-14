example : UInt8.toFin 42 = 42 := by simp
example : UInt16.toFin 42 = 42 := by simp
example : UInt32.toFin 42 = 42 := by simp
example : UInt64.toFin 42 = 42 := by simp
example : USize.toFin 42 = 42 := by simp
example : UInt8.toBitVec 42 = 42 := by simp
example : UInt16.toBitVec 42 = 42 := by simp
example : UInt32.toBitVec 42 = 42 := by simp
example : UInt64.toBitVec 42 = 42 := by simp
example : USize.toBitVec 42 = 42 := by simp
example : UInt8.ofBitVec 42 = 42 := by simp
example : UInt16.ofBitVec 42 = 42 := by simp
example : UInt32.ofBitVec 42 = 42 := by simp
example : UInt64.ofBitVec 42 = 42 := by simp
example : USize.ofBitVec 42 = 42 := by simp

example : (-1 : UInt8) = 255 := rfl
example : (-1 : UInt8) = 255 := by native_decide
example : (-1 : UInt16) = 65535 := rfl
example : (-1 : UInt16) = 65535 := by native_decide
example : (-1 : UInt32) = 4294967295 := rfl
example : (-1 : UInt32) = 4294967295 := by native_decide
example : (-1 : UInt64) = 18446744073709551615 := rfl
example : (-1 : UInt64) = 18446744073709551615 := by native_decide
example : (-1 : USize) = 18446744073709551615 := by
  apply USize.toBitVec_inj.1
  apply BitVec.eq_of_toNat_eq
  cases System.Platform.numBits_eq <;> simp_all
example : (-1 : USize) = 18446744073709551615 := by native_decide

-- TODO: turn into `by simp` when the relevant theory is in place
example : UInt8.ofFin 42 = 42 := rfl
example : UInt16.ofFin 42 = 42 := rfl
example : UInt32.ofFin 42 = 42 := rfl
example : UInt64.ofFin 42 = 42 := rfl
example : USize.ofFin 42 = 42 := rfl
