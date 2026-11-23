module
import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide


example (x y : BitVec 64) : BitVec.carry 64 x y false = (x.zeroExtend 65 + y.zeroExtend 65).msb := by
  bv_decide

example (x y : BitVec 64) : BitVec.carry 64 x y true = BitVec.carry 64 y x true := by
  bv_decide

example (x y : BitVec 64) (b : Bool) : BitVec.carry 32 x y b = BitVec.carry 32 y x b := by
  bv_decide

example (x : BitVec 64) (c : Bool) :
    x + BitVec.ofNat 64 c.toNat = x + (BitVec.ofBool c).zeroExtend 64 := by
  bv_decide

example (x : BitVec 64) : x + BitVec.zero 64 = x := by
  bv_decide
