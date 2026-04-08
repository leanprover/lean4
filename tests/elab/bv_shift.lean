import Std.Tactic.BVDecide

open BitVec

theorem shift_unit_1 {x y : BitVec 64} : x <<< 65 = y <<< 66 := by
  bv_decide

theorem shift_unit_1' {x y : BitVec 64} : BitVec.shiftLeft x 65 = y >>> 66 := by
  bv_decide

theorem shift_unit_2 {x y : BitVec 64} : x >>> 65 = y >>> 66 := by
  bv_decide

theorem shift_unit_2' {x y : BitVec 64} : BitVec.ushiftRight x 65 = y >>> 66 := by
  bv_decide

theorem shift_unit_3 {x : BitVec 64} : (x <<< 32) <<< 32 = (x >>> 32) >>> 32 := by
  bv_decide

theorem shift_unit_5 {x y z : BitVec 16} : (x <<< y) <<< z = (x <<< z) <<< y := by
  bv_decide

theorem shift_unit_6 {x y z : BitVec 16} : (x >>> y) >>> z = (x >>> z) >>> y := by
  bv_decide

theorem rotate_unit_1 {x : BitVec 64} : BitVec.rotateLeft x 0 = x := by
  bv_decide

theorem rotate_unit_2 {x : BitVec 64} : BitVec.rotateLeft x 64 = x := by
  bv_decide

theorem rotate_unit_3 {x : BitVec 64} : BitVec.rotateLeft x 16 = (BitVec.rotateLeft (BitVec.rotateLeft x 6) 10) := by
  bv_decide

theorem rotate_unit_4 {x : BitVec 64} : BitVec.rotateLeft x (64 + 16) = (BitVec.rotateLeft x 16) := by
  bv_decide

theorem rotate_unit_5 {x : BitVec 64} : BitVec.rotateRight x 0 = x := by
  bv_decide

theorem rotate_unit_6 {x : BitVec 64} : BitVec.rotateRight x 64 = x := by
  bv_decide

theorem rotate_unit_7 {x : BitVec 64} : BitVec.rotateRight x 16 = (BitVec.rotateRight (BitVec.rotateRight x 6) 10) := by
  bv_decide

theorem rotate_unit_8 {x : BitVec 64} : BitVec.rotateRight x (64 + 16) = (BitVec.rotateRight x 16) := by
  bv_decide

theorem shift_unit_7 {x : BitVec 64} : BitVec.sshiftRight x 65 = BitVec.sshiftRight x 66 := by
  bv_decide

theorem shift_unit_8 {x : BitVec 64} (h : BitVec.slt 0 x) : BitVec.sshiftRight x 32 = x >>> 32 := by
  bv_decide

theorem shift_unit_9 {x y : BitVec 32} (h : BitVec.slt 0 x) : BitVec.sshiftRight' x y = x >>> y := by
  bv_decide
