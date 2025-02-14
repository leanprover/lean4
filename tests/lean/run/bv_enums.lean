import Std.Tactic.BVDecide

namespace Ex1

inductive State where
  | sa
  | sb
  | sc
  | sd
  | se
  | sf
  | sg
  | sh
  | si
  | sj
  | sk
  | sl
  | sm
  | sn
  | so
  | sp

/-- info: _root_.Ex1.State.enumToBitVec : State → BitVec 4 -/
#guard_msgs in
#check State.enumToBitVec

/--
info: _root_.Ex1.State.eq_iff_enumToBitVec_eq (x y : State) : x = y ↔ x.enumToBitVec = y.enumToBitVec
-/
#guard_msgs in
#check State.eq_iff_enumToBitVec_eq

/-- info: _root_.Ex1.State.enumToBitVec_le (x : State) : x.enumToBitVec ≤ 15#4 -/
#guard_msgs in
#check State.enumToBitVec_le

structure Pair where
  x : BitVec 16
  s : State

-- large inductive
example (a b c : Pair) (h1 : a = b) (h2 : b.x < c.x) (h3 : b.s = c.s) : a.s = c.s ∧ a.x < c.x := by
  bv_normalize
  bv_decide

end Ex1

namespace Ex2

inductive State where
  | s1
  | s2

structure Pair where
  x : BitVec 16
  s : State
  h : s = .s1 ↔ x = 0

-- handling constants
example (a : Pair) (h : a.x > 0) : a.s = .s2 := by
  bv_decide

/--
error: The prover found a counterexample, consider the following assignment:
x = 0#16
s = State.s1
-/
#guard_msgs in
example (x : BitVec 16) (s : State) (h1 : s = .s1 ↔ x = 0) (h : s = .s1) : x > 0 := by
  bv_decide

end Ex2

namespace Ex3

-- adding ≤ domainSize - 1 hypothesis

inductive State where
  | s1
  | s2
  | s3

example (s : State) (h : s ≠ .s1 ∧ s ≠ .s2 ∧ s ≠ .s3) : False := by
  bv_decide

structure Pair where
  s : State
  x : BitVec 16
  h1 : s ≠ .s1 ↔ x > 0
  h2 : s ≠ .s2 ↔ x > 1
  h3 : s ≠ .s3 ↔ x > 2

example (a : Pair) (h : a.x ≥ 100) : False := by
  bv_decide

end Ex3
