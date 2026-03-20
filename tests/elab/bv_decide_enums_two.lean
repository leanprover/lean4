import Std.Tactic.BVDecide

inductive State : Type
| A : State
| B : State


def myFunc (s : State) : Bool :=
  match s with
  | .A => true
  | _ => false

theorem test (h : s ≠ State.B) : myFunc s = true := by
  simp only [myFunc]
  bv_decide
