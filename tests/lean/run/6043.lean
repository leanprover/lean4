import Std.Tactic.BVDecide

theorem extracted_1 (x : BitVec 32) :
  BitVec.ofBool (x != 51#32) &&& BitVec.ofBool (x != 50#32) =
    BitVec.ofBool (4294967294#32 > x + 4294967244#32) := by
  bv_decide
