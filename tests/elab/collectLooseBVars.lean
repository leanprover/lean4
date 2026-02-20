import Lean
/-!
# Tests of `Expr.collectLooseBVars`
-/

open Lean Elab Command

elab "#test " offset:num " => " t:term : command => runTermElabM fun xs => do
  let e ← Term.elabTermAndSynthesize t none
  let e' := e.abstract xs
  let o := offset.getNat
  let bvars := (e'.collectLooseBVars o).toArray.insertionSort (· < ·)
  logInfo m!"bvars: {bvars}"

variable (x y z : Nat)

/-!
Testing some expressions without binders.
-/

/-- info: bvars: [2] -/
#guard_msgs in #test 0 => x
/-- info: bvars: [1] -/
#guard_msgs in #test 0 => y
/-- info: bvars: [0] -/
#guard_msgs in #test 0 => z
/-- info: bvars: [0, 1, 2] -/
#guard_msgs in #test 0 => x+y+z

/-!
Testing offsets.
-/

/-- info: bvars: [2] -/
#guard_msgs in #test 0 => x
/-- info: bvars: [1] -/
#guard_msgs in #test 1 => x
/-- info: bvars: [0] -/
#guard_msgs in #test 2 => x
/-- info: bvars: [] -/
#guard_msgs in #test 3 => x
/-- info: bvars: [0, 1, 2] -/
#guard_msgs in #test 0 => x+y+z
/-- info: bvars: [0, 1] -/
#guard_msgs in #test 1 => x+y+z
/-- info: bvars: [0] -/
#guard_msgs in #test 2 => x+y+z
/-- info: bvars: [] -/
#guard_msgs in #test 3 => x+y+z

/-!
Testing binders.
Notice that even though `x` is under a binder (so it is `.bvar 3`) it gets reported as `2`.
-/
/-- info: bvars: [2] -/
#guard_msgs in #test 0 => fun a => a + x
/-- info: bvars: [2] -/
#guard_msgs in #test 0 => (a : Nat) → Fin (a + x)
/-- info: bvars: [2] -/
#guard_msgs in #test 0 => let a := 2; a + x
/-- info: bvars: [2] -/
#guard_msgs in #test 0 => fun a => let v := x; fun b => a + v + b + x
