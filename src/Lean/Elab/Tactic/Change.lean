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

private def elabChangeDefaultError (p tgt : Expr) : MetaM MessageData := do
  return m!"\
    'change' tactic failed, pattern{indentExpr p}\n\
    is not definitionally equal to target{indentExpr tgt}"

/--
Elaborates the pattern `p` and ensures that it is defeq to `e`.
Emulates `(show p from ?m : e)`, returning the type of `?m`, but `e` and `p` do not need to be types.
Unlike `(show p from ?m : e)`, this can assign synthetic opaque metavariables appearing in `p`.
-/
def elabChange (e : Expr) (p : Term) (mkDefeqError : Expr → Expr → MetaM MessageData := elabChangeDefaultError) :
    TacticM Expr := do
  let p ← runTermElab do
    let p ← Term.elabTermEnsuringType p (← inferType e)
    unless ← isDefEq p e do
      /-
      Sometimes isDefEq can fail due to postponed elaboration problems.
      We synthesize pending synthetic mvars while allowing typeclass instances to be postponed,
      which might enable solving for them with an additional `isDefEq`.
      -/
      Term.synthesizeSyntheticMVars (postpone := .partial)
      discard <| isDefEq p e
    pure p
  withAssignableSyntheticOpaque do
    unless ← isDefEq p e do
      throwError MessageData.ofLazyM (es := #[p, e]) do
        let (p, tgt) ← addPPExplicitToExposeDiff p e
        mkDefeqError p tgt
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
        let (hTy', mvars) ← withCollectingNewGoalsFrom (elabChange (← h.getType) newType) (← getMainTag) `change
        liftMetaTactic fun mvarId => do
          return (← mvarId.changeLocalDecl h hTy') :: mvars)
      (atTarget := do
        let (tgt', mvars) ← withCollectingNewGoalsFrom (elabChange (← getMainTarget) newType) (← getMainTag) `change
        liftMetaTactic fun mvarId => do
          return (← mvarId.replaceTargetDefEq tgt') :: mvars)
      (failed := fun _ => throwError "'change' tactic failed")

end Lean.Elab.Tactic
