import Lean.Elab.Command

/-!
# Issue 4406: make sure `pp.instantiateMVars` has an effect
-/

open Lean Meta

set_option pp.mvars false

/-- info: ?_ -/
#guard_msgs in
set_option pp.instantiateMVars false in
run_meta do
  let mvarId ← mkFreshExprMVar (.some (.const ``Nat []))
  mvarId.mvarId!.assign (mkNatLit 0)
  logInfo m!"{mvarId}"

/-- info: 0 -/
#guard_msgs in
run_meta do
  let mvarId ← mkFreshExprMVar (.some (.const ``Nat []))
  mvarId.mvarId!.assign (mkNatLit 0)
  logInfo m!"{mvarId}"
