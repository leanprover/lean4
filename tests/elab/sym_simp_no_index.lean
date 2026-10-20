import Std.Tactic.BVDecide
import Lean
set_option warn.sorry false

/-!
Tests for `Sym` pattern matching against constant-folded targets.

`no_index` annotations (e.g. `BitVec (no_index _)` in `bv_normalize` theorems such as
`Std.Tactic.BVDecide.Normalize.BitVec.append_const_right`) make the discrimination tree emit
wildcard keys, so retrieval succeeds. The matcher must then solve `Nat` constraints such as
`w1 + w2 =?= 16` where the target width was constant-folded: `process` postpones such
quasi-offset constraints (see `isQuasiOffsetCnstr`) until phase 1 assigns the pattern
variables, and the instantiated constraint (e.g. `8 + 8 =?= 16`) is solved by `isDefEqOffset`,
the structural counterpart of `Meta.isDefEqOffset`.
-/

open Lean Meta Lean.Meta.Sym Lean.Meta.Sym.Simp

def target1 (a : BitVec 8) : BitVec 24 := (a ++ 1#8) ++ 2#8

def target2 (a : BitVec 8) : BitVec 24 := 1#8 ++ (2#8 ++ a)

/-- Rewrites the value of `declName` with `thmName` after constant folding ground subterms. -/
def check (declName thmName : Name) : MetaM Unit := do
  let value := (← getConstInfoDefn declName).value
  lambdaTelescope value fun _ body => do SymM.run do
    let thm ← mkTheoremFromDecl thmName
    let thms := ({} : Theorems).insert thm
    let methods : Methods := { post := thms.rewrite }
    let body ← share body
    let body ← dsimp body { pre := DSimp.evalGround }
    let r ← simp body methods {}
    logInfo m!"before: {body}\nafter:  {Result.getResultExpr body r}"

/--
info: before: a ++ 1#8 ++ 2#8
after:  BitVec.cast ⋯ (a ++ (1#8 ++ 2#8))
-/
#guard_msgs in
run_meta check ``target1 ``Std.Tactic.BVDecide.Normalize.BitVec.append_const_right

/--
info: before: 1#8 ++ (2#8 ++ a)
after:  BitVec.cast ⋯ (1#8 ++ 2#8 ++ a)
-/
#guard_msgs in
run_meta check ``target2 ``Std.Tactic.BVDecide.Normalize.BitVec.append_const_left

/-!
Minimal `Nat`-only regression: `x` is bound by the first argument, and the annotated
`x + x` must then match the folded literal `16`. Without `no_index` the discrimination
tree would not even retrieve the theorem.
-/

opaque p2 : Nat → Nat → Prop
theorem p2_thm (x : Nat) : p2 x (no_index (x + x)) = True := sorry

/-- info: step: True -/
#guard_msgs in
run_meta SymM.run do
  let e ← share (mkApp2 (mkConst ``p2) (mkNatLit 8) (mkNatLit 16))
  let thm ← mkTheoremFromDecl ``p2_thm
  let r ← SimpM.run' (thm.rewrite e)
  match r with
  | .step e' _ _ _ => logInfo m!"step: {e'}"
  | _ => logInfo "rfl"

-- The nonlinear constraint must still fail when the arithmetic does not hold.
/-- info: rfl -/
#guard_msgs in
run_meta SymM.run do
  let e ← share (mkApp2 (mkConst ``p2) (mkNatLit 8) (mkNatLit 17))
  let thm ← mkTheoremFromDecl ``p2_thm
  let r ← SimpM.run' (thm.rewrite e)
  match r with
  | .step e' _ _ _ => logInfo m!"step: {e'}"
  | _ => logInfo "rfl"

/-! `isDefEqS` folds ground `Nat` arithmetic via `isDefEqOffset`. -/

/--
info: 8 + 8 =?= 16: true
---
info: 8 + 8 =?= 17: false
---
info: x + 2 =?= x + 1 + 1: true
-/
#guard_msgs in
run_meta SymM.run do
  let add8 ← share (← mkAppM ``HAdd.hAdd #[mkNatLit 8, mkNatLit 8])
  logInfo m!"8 + 8 =?= 16: {← isDefEqS add8 (← share (mkNatLit 16))}"
  logInfo m!"8 + 8 =?= 17: {← isDefEqS add8 (← share (mkNatLit 17))}"
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let lhs ← share (← mkAppM ``HAdd.hAdd #[x, mkNatLit 2])
    let rhs ← share (← mkAppM ``HAdd.hAdd #[← mkAppM ``HAdd.hAdd #[x, mkNatLit 1], mkNatLit 1])
    logInfo m!"x + 2 =?= x + 1 + 1: {← isDefEqS lhs rhs}"
