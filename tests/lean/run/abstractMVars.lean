import Lean
/-!
# Tests of the `Lean.Meta.abstractMVars` procedure
-/

open Lean Meta

/-!
The following example used to abstract `levelMVar` even though it was assigned.
The issue was that the procedure failed to instantiateMVars in the types of metavariables.

Reported on Zulip: https://leanprover.zulipchat.com/#narrow/channel/239415-metaprogramming-.2F-tactics/topic/.60abstractMVars.60.20not.20instantiating.20level.20mvars/near/541918246
-/

/-- info: [] -/
#guard_msgs in
run_meta
  let levelMVar ← mkFreshLevelMVar
  let mvar ← mkFreshExprMVar (some (mkSort levelMVar))
  discard <| isDefEq (mkSort levelMVar) (mkSort (mkLevelParam `u))
  let mvar ← instantiateMVars mvar
  let abstractResult ← abstractMVars mvar
  Lean.logInfo m!"{abstractResult.paramNames}"
