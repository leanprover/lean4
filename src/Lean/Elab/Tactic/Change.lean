/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.Meta.Tactic.Replace
import Lean.Elab.Tactic.Location

namespace Lean.Elab.Tactic
open Meta
/-!
# Implementation of the `change` tactic
-/

/-- Elaborates the pattern `p` and ensures that it is defeq to `e`. -/
def elabChange (e : Expr) (p : Term) : TacticM Expr := do
  let mvarCounterSaved := (← getMCtx).mvarCounter
  let p ← elabTermEnsuringType p (← inferType e) (mayPostpone := true)
  -- Discretionary `isDefEq` before synthesizing remaining metavariables. Save the result to avoid a final `isDefEq` check if it passes.
  let defeq ← isDefEq p e
  Term.synthesizeSyntheticMVarsNoPostponing
  withAssignableSyntheticOpaque do
    unless ← pure defeq <||> isDefEq p e do
      let (p, tgt) ← addPPExplicitToExposeDiff p e
      throwError "\
        'change' tactic failed, pattern{indentExpr p}\n\
        is not definitionally equal to target{indentExpr tgt}"
    logUnassignedAndAbort (← filterOldMVars (← getMVars p) mvarCounterSaved)
    instantiateMVars p

/-- `change` can be used to replace the main goal or its hypotheses with
different, yet definitionally equal, goal or hypotheses.

For example, if `n : Nat` and the current goal is `⊢ n + 2 = 2`, then
```lean
change _ + 1 = _
```
changes the goal to `⊢ n + 1 + 1 = 2`.

The tactic also applies to hypotheses. If `h : n + 2 = 2` and `h' : n + 3 = 4`
are hypotheses, then
```lean
change _ + 1 = _ at h h'
```
changes their types to be `h : n + 1 + 1 = 2` and `h' : n + 2 + 1 = 4`.

Change is like `refine` in that every placeholder needs to be solved for by unification,
but using named placeholders or `?_` results in `change` to creating new goals.

The tactic `show e` is interchangeable with `change e`, where the pattern `e` is applied to
the main goal. -/
@[builtin_tactic change] elab_rules : tactic
  | `(tactic| change $newType:term $[$loc:location]?) => do
    withLocation (expandOptLocation (Lean.mkOptionalNode loc))
      (atLocal := fun h => do
        let hTy' ← elabChange (← h.getType) newType
        liftMetaTactic1 fun mvarId => do
          mvarId.changeLocalDecl h hTy')
      (atTarget := do
        let tgt' ← elabChange (← getMainTarget) newType
        liftMetaTactic1 fun mvarId => do
          mvarId.replaceTargetDefEq tgt')
      (failed := fun _ => throwError "'change' tactic failed")

end Lean.Elab.Tactic
