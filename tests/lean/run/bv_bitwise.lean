import Std.Tactic.BVDecide

open BitVec

theorem bitwise_unit_1 {x y : BitVec 64} : ~~~(x &&& y) = (~~~x ||| ~~~y) := by
  bv_decide

theorem bitwise_unit_1' {x y : BitVec 64} : ~~~(BitVec.and x y) = ((BitVec.not x) ||| ~~~y) := by
  bv_decide

theorem bitwise_unit_2 {x : BitVec 64} : x ^^^ x = 0 := by
  bv_decide

theorem bitwise_unit_2' {x : BitVec 64} : (BitVec.xor x x) = 0 := by
  bv_decide

theorem bitwise_unit_3 {x : BitVec 64} : (x ^^^ x).getLsbD 32 = false := by
  bv_decide

theorem bitwise_unit_4 {x : BitVec 64} : (x ^^^ ~~~x).getLsbD 32 = true := by
  bv_decide

theorem bitwise_unit_5 {x : BitVec 64} : (x ^^^ ~~~x).getLsbD 128 = false := by
  bv_decide

theorem bitwise_unit_6 {x : BitVec 64} : (x ^^^ ~~~x).getLsbD 63 = (x ^^^ ~~~x).msb := by
  bv_decide

theorem bitwise_unit_7 (x : BitVec 32) : x ^^^ 123#32 = 123#'(by decide) ^^^ x := by
  bv_decide

theorem bitwise_unit_8 (x : BitVec 32) : BitVec.ofBool (x.getLsbD 0) = x.extractLsb' 0 1 := by
  bv_decide

theorem bitwise_unit_9 (x y : BitVec 32) :
    BitVec.ofBool (x.getLsbD 0 ^^ y.getLsbD 0) = BitVec.ofBool ((x ^^^ y).getLsbD 0) := by
  bv_decide

theorem bitwise_unit_10 (x : BitVec 2) : (x.getMsbD 0) = x.msb := by
  bv_decide
