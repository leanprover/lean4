import Std.Tactic.BVDecide


/-- info: PUnit.enumToBitVec.{u} : PUnit → BitVec 0 -/
#guard_msgs in
#check _root_.PUnit.enumToBitVec

/--
info: PUnit.eq_iff_enumToBitVec_eq.{u} (x y : PUnit) : x = y ↔ x.enumToBitVec = y.enumToBitVec
-/
#guard_msgs in
#check PUnit.eq_iff_enumToBitVec_eq

/-- info: PUnit.enumToBitVec_le.{u} (x : PUnit) : x.enumToBitVec ≤ 0#0 -/
#guard_msgs in
#check PUnit.enumToBitVec_le

def test1 (x : PUnit) : Bool :=
  match x with
  | _ => false

def test2 (x : PUnit.{1}) : Bool :=
  match x with
  | _ => false

example (_a : PUnit) : True := by
  bv_normalize

example (_a : PUnit.{1}) : True := by
  bv_normalize

example (_a : PUnit) (h : test1 x = true) : False := by
  unfold test1 at h
  bv_normalize

example (_a : PUnit.{1}) (h : test2 x = true) : False := by
  unfold test2 at h
  bv_normalize

inductive PBool : Type u where
  | true
  | false

/-- info: PBool.enumToBitVec.{u} : PBool → BitVec 1 -/
#guard_msgs in
#check PBool.enumToBitVec

/--
info: PBool.eq_iff_enumToBitVec_eq.{u} (x y : PBool) : x = y ↔ x.enumToBitVec = y.enumToBitVec
-/
#guard_msgs in
#check PBool.eq_iff_enumToBitVec_eq

/-- info: PBool.enumToBitVec_le.{u} (x : PBool) : x.enumToBitVec ≤ 1#1 -/
#guard_msgs in
#check PBool.enumToBitVec_le

def test3 (x : PBool) : Bool :=
  match x with
  | .false => false
  | .true => false

def test4 (x : PBool.{1}) : Bool :=
  match x with
  | .false => false
  | .true => false

def test5 (x : PBool) : Bool :=
  match x with
  | .true => false
  | _ => false

def test6 (x : PBool.{1}) : Bool :=
  match x with
  | .true => false
  | _ => false

example (_a : PBool) : True := by
  bv_normalize

example (_a : PBool.{1}) : True := by
  bv_normalize

example (x : PBool) (h : test3 x = true) : False := by
  unfold test3 at h
  bv_normalize

example (x : PBool.{1}) (h : test4 x = true) : False := by
  unfold test4 at h
  bv_normalize

example (x : PBool) (h : test5 x = true) : False := by
  unfold test5 at h
  bv_normalize

example (x : PBool.{1}) (h : test6 x = true) : False := by
  unfold test6 at h
  bv_normalize

/--
error: The prover found a counterexample, consider the following assignment:
x = PBool.false
-/
#guard_msgs in
example (x : PBool.{1}) : x = .true := by
  bv_decide

/--
error: The prover found a counterexample, consider the following assignment:
x = PBool.false
-/
#guard_msgs in
example (x : PBool) : x = .true := by
  bv_decide

inductive State : Type u where
  | s1
  | s2
  | s3

example (s : State) (h : s ≠ .s1 ∧ s ≠ .s2 ∧ s ≠ .s3) : False := by
  bv_decide

example (s : State.{1}) (h : s ≠ .s1 ∧ s ≠ .s2 ∧ s ≠ .s3) : False := by
  bv_decide
