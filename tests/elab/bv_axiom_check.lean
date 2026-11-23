import Std.Tactic.BVDecide

open BitVec

theorem bv_axiomCheck (x y z : BitVec 1) : x < y → y < z → x < z := by bv_decide

/--
info: 'bv_axiomCheck' depends on axioms: [propext, Classical.choice, Quot.sound, bv_axiomCheck._native.bv_decide.ax_1_5]
-/
#guard_msgs in
#print axioms bv_axiomCheck
