/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.Meta.KAbstract
import Lean.Meta.Tactic.Replace
import Lean.Elab.Tactic.Location

namespace Lean.Elab.Tactic
open Meta
/-!
# Implementations of the `change` tactics
-/

/--
Elaborates the pattern `p` and ensures that it is defeq to `e`.
Emulates `(show p from ?m : e)`, returning the type of `?m`, but `e` and `p` do not need to be types.
Unlike `(show p from ?m : e)`, this can assign synthetic opaque metavariables appearing in `p`.
-/
def elabChange (e : Expr) (p : Term) : TacticM Expr := do
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
      let (p, e) ← addPPExplicitToExposeDiff p e
      throwError "\
        'change' tactic failed, pattern{indentExpr p}\n\
        is not definitionally equal to target{indentExpr e}"
    instantiateMVars p

@[builtin_tactic change] elab_rules : tactic
  | `(tactic| change $newType:term $[$loc:location]?) => do
    withLocation (expandOptLocation (Lean.mkOptionalNode loc))
      (atLocal := fun h => do
        let (hTy', mvars) ← withCollectingNewGoalsFrom (elabChange (← h.getType) newType) (← getMainTag) `change
        liftMetaTactic fun mvarId => do
          if ← occursCheck mvarId hTy' then
            return (← mvarId.changeLocalDecl h hTy') :: mvars
          else
            throwError "occurs check failed, expression{indentExpr hTy'}\ncontains the goal {Expr.mvar mvarId}")
      (atTarget := do
        let (tgt', mvars) ← withCollectingNewGoalsFrom (elabChange (← getMainTarget) newType) (← getMainTag) `change
        liftMetaTactic fun mvarId => do
          if ← occursCheck mvarId tgt' then
            return (← mvarId.replaceTargetDefEq tgt') :: mvars
          else
            throwError "occurs check failed, expression{indentExpr tgt'}\ncontains the goal {Expr.mvar mvarId}")
      (failed := fun _ => throwError "'change' tactic failed")

/--
Replaces each occurrence of `p` in `e` with `t`.
This is roughly like doing `rewrite [show p = t by rfl]` on `e`, but it does not require a type-correct motive.
-/
def elabChangeMatching (e : Expr) (p t : Term) : TacticM Expr := do
  -- Set `mayPostpone := true` like when elaborating `rewrite` rules.
  let (p, t) ← runTermElab (mayPostpone := true) do
    let p ← Term.elabTerm p none
    let t ← Term.elabTermEnsuringType t (← inferType p)
    return (p, t)
  let p ← instantiateMVars p
  let e' ← kabstract e p
  unless e'.hasLooseBVars do
    throwError "\
      'change_matching' tactic failed, did not find instance of the pattern{indentExpr p}\n\
      in the expression{indentExpr e}"
  -- Now that `kabstract` has unified `p` with a subterm of `e`, make sure elaboration is complete.
  Term.synthesizeSyntheticMVarsNoPostponing
  withAssignableSyntheticOpaque do
    unless ← isDefEq p t do
      let (p, t) ← addPPExplicitToExposeDiff p t
      throwError "\
        'change_matching' tactic failed, pattern{indentExpr p}\n\
        is not definitionally equal to replacement{indentExpr t}"
    instantiateMVars (e'.instantiate1 t)

@[builtin_tactic changeMatching] elab_rules : tactic
  | `(tactic| change_matching $p:term with $t:term $[$loc:location]?) => do
    withLocation (expandOptLocation (mkOptionalNode loc))
      (atLocal := fun h => do
        let hTy ← h.getType
        let (hTy', mvars) ← withCollectingNewGoalsFrom (elabChangeMatching hTy p t) (← getMainTag) `change_matching
        liftMetaTactic fun mvarId => do
          if ← occursCheck mvarId hTy' then
            return (← mvarId.changeLocalDecl h hTy') :: mvars
          else
            throwError "occurs check failed, expression{indentExpr hTy'}\ncontains the goal {Expr.mvar mvarId}")
      (atTarget := do
        let (tgt', mvars) ← withCollectingNewGoalsFrom (elabChangeMatching (← getMainTarget) p t) (← getMainTag) `change_matching
        liftMetaTactic fun mvarId => do
          if ← occursCheck mvarId tgt' then
            return (← mvarId.replaceTargetDefEq tgt') :: mvars
          else
            throwError "occurs check failed, expression{indentExpr tgt'}\ncontains the goal {Expr.mvar mvarId}")
      (failed := fun _ => throwError "'change_matching' tactic failed")

end Lean.Elab.Tactic
