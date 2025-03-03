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

open Lean Elab Tactic BVDecide



theorem thm :
  Foo.f1.match_1 (fun _ => α) x h1 h2 h3
    =
  bif Foo.enumToBitVec x == 0#2 then h1 ()
  else bif Foo.enumToBitVec x == 1#2 then h2 ()
  else bif Foo.enumToBitVec x == 2#2 then h3 () else h3 () :=
  by cases x <;> rfl

theorem thm :
  Foo.f1.match_1 (fun _ => α) x h1 h2 h3
    =
  bif Foo.enumToBitVec x == 0#2 then h1 ()
  else bif Foo.enumToBitVec x == 1#2 then h2 ()
  else bif Foo.enumToBitVec x == 2#2 then h3 () else h3 () :=
  Foo.recOn (motive := fun x =>
      (match x with
        | Foo.a => h1 ()
        | Foo.b => h2 ()
        | Foo.c => h3 ()) =
        bif x.enumToBitVec == 0#2 then h1 ()
        else bif x.enumToBitVec == 1#2 then h2 () else bif x.enumToBitVec == 2#2 then h3 () else h3 ())
    x (Eq.refl (h1 ())) (Eq.refl (h2 ())) (Eq.refl (h3 ()))

#print thm

set_option pp.explicit true
#print Foo.f1.match_1

/-- info: true -/
#guard_msgs in
#eval show MetaM _ from do
  let res ← Lean.Elab.Tactic.BVDecide.Frontend.Normalize.matchIsSupported ``Foo.f1.match_1
  return res matches some .simple

/-- info: true -/
#guard_msgs in
#eval show MetaM _ from do
  let res ← Lean.Elab.Tactic.BVDecide.Frontend.Normalize.matchIsSupported ``Foo.f2.match_1
  return res matches none

/-- info: true -/
#guard_msgs in
#eval show MetaM _ from do
  let res ← Lean.Elab.Tactic.BVDecide.Frontend.Normalize.matchIsSupported ``Foo.f3.match_1
  return res matches none

/-- info: true -/
#guard_msgs in
#eval show MetaM _ from do
  let res ← Lean.Elab.Tactic.BVDecide.Frontend.Normalize.matchIsSupported ``Foo.f4.match_1
  return res matches none

/-- info: true -/
#guard_msgs in
#eval show MetaM _ from do
  let res ← Lean.Elab.Tactic.BVDecide.Frontend.Normalize.matchIsSupported ``Foo.f4.match_2
  return res matches none

end Ex4
