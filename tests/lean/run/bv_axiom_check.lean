import Std.Tactic.BVDecide

open BitVec

theorem bv_axiomCheck (x y : BitVec 1) : x + y = y + x := by
  bv_decide

/-- info: 'bv_axiomCheck' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bv_axiomCheck
