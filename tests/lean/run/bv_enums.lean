import Std.Tactic.BVDecide
import Lean.Elab.Tactic.BVDecide

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

namespace Ex4

-- pattern matching

inductive Foo where
  | a
  | b
  | c

def Foo.f1 : Foo → Foo
  | .a => .b
  | .b => .c
  | .c => .a

def Foo.f2 : Foo → Foo
  | .a => .b
  | _ => .c

def Foo.f3 (f : Foo) (h : f ≠ .a) : Foo :=
  match f with
  | .b => .c
  | .c => .c

def Foo.f4 (f : Foo) (h : ∀ f : Foo, f ≠ .a) : Foo :=
  match h2 : f with
  | .a =>
    have : False := by
      specialize h f
      contradiction
    nomatch this
  | .b => .c
  | .c => .c

open Lean Meta

/-- info: true -/
#guard_msgs in
#eval show MetaM _ from do
  let res ← Lean.Elab.Tactic.BVDecide.Frontend.Normalize.isSupportedMatch ``Foo.f1.match_1
  return res matches some (.simpleEnum ..)

/-- info: true -/
#guard_msgs in
#eval show MetaM _ from do
  let res ← Lean.Elab.Tactic.BVDecide.Frontend.Normalize.isSupportedMatch ``Foo.f2.match_1
  return res matches none

/-- info: true -/
#guard_msgs in
#eval show MetaM _ from do
  let res ← Lean.Elab.Tactic.BVDecide.Frontend.Normalize.isSupportedMatch ``Foo.f3.match_1
  return res matches none

/-- info: true -/
#guard_msgs in
#eval show MetaM _ from do
  let res ← Lean.Elab.Tactic.BVDecide.Frontend.Normalize.isSupportedMatch ``Foo.f4.match_1
  return res matches none

/-- info: true -/
#guard_msgs in
#eval show MetaM _ from do
  let res ← Lean.Elab.Tactic.BVDecide.Frontend.Normalize.isSupportedMatch ``Foo.f4.match_2
  return res matches none

def Foo.f5 : Foo → BitVec 64
  | .a => 37
  | .b => 42
  | .c => 22

example : ∀ (x y : Foo), x.f5 = y.f5 → x = y := by
  unfold Foo.f5
  bv_decide

example (foo : Foo) : foo.f1 ≠ foo := by
  unfold Foo.f1
  bv_decide

example (x : Foo) : x.f1.f1.f1 = x := by
  unfold Foo.f1
  bv_decide

example (h : f = Foo.a): Foo.a.f1 ≠ f := by
  unfold Foo.f1
  bv_decide

end Ex4

namespace PingPong

inductive Direction where
  | goingDown
  | goingUp

structure State where
  val : BitVec 16
  low : BitVec 16
  high : BitVec 16
  direction : Direction

def State.step (s : State) : State :=
  match s.direction with
  | .goingDown =>
    if s.val = s.low then
      { s with direction := .goingUp }
    else
      { s with val := s.val - 1 }
  | .goingUp =>
    if s.val = s.high then
      { s with direction := .goingDown }
    else
      { s with val := s.val + 1 }

def State.steps (s : State) (n : Nat) : State :=
  match n with
  | 0 => s
  | n + 1 => (State.steps s n).step

def Inv (s : State) : Prop := s.low ≤ s.val ∧ s.val ≤ s.high ∧ s.low < s.high

example (s : State) (h : Inv s) (n : Nat) : Inv (State.steps s n) := by
  induction n with
  | zero => simp only [State.steps, Inv] at *; bv_decide
  | succ n ih =>
    simp only [State.steps, State.step, Inv] at *
    bv_decide

end PingPong
