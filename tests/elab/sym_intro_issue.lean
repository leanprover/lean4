/-
MWE: `Sym.introCore` assigns the original mvar even when no binders are introduced.
`Sym.intros` returns `.failed` but the mvar is secretly assigned.

The bug is in `introCore.finalize`: it unconditionally creates an `auxMVar` with a
delayed assignment and assigns the original mvar to it, even when `fvars` is empty
(no binders were introduced). Then `intros` checks `fvars.isEmpty` and returns `.failed`,
but the mvar is already assigned. Downstream code that checks `isAssigned` (e.g. VC filters
in mvcgen') will wrongly think the goal is solved.

Fix: guard `finalize` with `if fvars.isEmpty then return (#[], mvarId)`.
-/
import Lean

-- Demonstrate the bug by calling `Sym.intros` on a non-forall goal.
-- With the fix in `introCore.finalize`, this prints "GOOD".
-- Without the fix, it prints "BUG".
/--
info: before intros: isAssigned=false
intros returned .failed (as expected for non-forall target)
after intros: isAssigned=false, isDelayedAssigned=false
GOOD: mvar is still unassigned
-/
#guard_msgs in
open Lean Meta Sym in
#eval show MetaM Unit from do
  let goal ← mkFreshExprMVar (mkConst ``False) .syntheticOpaque
  let goalId := goal.mvarId!
  IO.println s!"before intros: isAssigned={← goalId.isAssigned}"
  let result ← Sym.SymM.run (Sym.intros goalId)
  match result with
  | .failed => IO.println "intros returned .failed (as expected for non-forall target)"
  | .goal _ _ => IO.println "intros returned .goal (unexpected)"
  IO.println s!"after intros: isAssigned={← goalId.isAssigned}, isDelayedAssigned={← goalId.isDelayedAssigned}"
  if (← goalId.isAssigned) then
    IO.println "BUG: mvar was assigned despite intros returning .failed"
  else
    IO.println "GOOD: mvar is still unassigned"
