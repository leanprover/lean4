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

/--
error: None of the hypotheses are in the supported BitVec fragment after applying preprocessing.
There are three potential reasons for this:
1. If you are using custom BitVec constructs simplify them to built-in ones.
2. If your problem is using only built-in ones it might currently be out of reach.
   Consider expressing it in terms of different operations that are better supported.
3. The original goal was reduced to False and is thus invalid.
-/
#guard_msgs in
theorem wtf (a : Bool) : r' a := by
  simp [r']
  bv_decide
