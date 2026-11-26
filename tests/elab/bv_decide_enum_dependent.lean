import Std.Tactic.BVDecide

inductive Bar : Type
| A : Bar
| B : Bar
| C : Bar -- Requires extra variant in enum
deriving DecidableEq
structure Foo where
  state : Bar
  num : BitVec 1
deriving DecidableEq
def r' (b : Bool)
  : Bool :=
  -- Two inline if-statements
  let a : Foo :=
    if b then { state := .A, num := 0 }
    else { state := .B, num := 0 }
  let x : Foo :=
    if a.state = .A then { state := .A, num := 0}
    else { state := .B, num := 0 }
  x.num.getLsbD 0

/-- error: The prover found a counterexample, consider the following assignment: -/
#guard_msgs in
theorem wtf (a : Bool) : r' a := by
  simp [r']
  bv_decide
