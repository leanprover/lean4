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

-- TODO: turn into `by simp` when the relevant theory is in place
example : UInt8.ofFin 42 = 42 := rfl
example : UInt16.ofFin 42 = 42 := rfl
example : UInt32.ofFin 42 = 42 := rfl
example : UInt64.ofFin 42 = 42 := rfl
example : USize.ofFin 42 = 42 := rfl
