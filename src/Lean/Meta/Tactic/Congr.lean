/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.CongrTheorems
import Lean.Meta.Tactic.Assert
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Assumption

namespace Lean
open Meta

/--
Preprocessor before applying congruence theorem.
Tries to close new goals using `Eq.refl`, `HEq.refl`, and `assumption`.
It also tries to apply `heq_of_eq`.
-/
def MVarId.congrPre (mvarId : MVarId) : MetaM (Option MVarId) := do
  let mvarId ← mvarId.heqOfEq
  try mvarId.refl; return none catch _ => pure ()
  try mvarId.hrefl; return none catch _ => pure ()
  if (← mvarId.assumptionCore) then return none
  return some mvarId

/--
Asserts the given congruence theorem as fresh hypothesis, and then applies it.
Return the `fvarId` for the new hypothesis and the new subgoals.
-/
private def applyCongrThm? (mvarId : MVarId) (congrThm : CongrTheorem) : MetaM (List MVarId) := do
  let mvarId ← mvarId.assert (← mkFreshUserName `h_congr_thm) congrThm.type congrThm.proof
  let (fvarId, mvarId) ← mvarId.intro1P
  let mvarIds ← mvarId.apply (mkFVar fvarId) { synthAssignedInstances := false }
  mvarIds.mapM fun mvarId => mvarId.tryClear fvarId

/--
Try to apply a `simp` congruence theorem.
-/
def MVarId.congr? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  mvarId.withContext do commitWhenSomeNoEx? do
    mvarId.checkNotAssigned `congr
    let target ← mvarId.getType'
    let some (_, lhs, _) := target.eq? | return none
    let lhs := lhs.cleanupAnnotations
    unless lhs.isApp do return none
    let some congrThm ← mkCongrSimp? lhs.getAppFn (subsingletonInstImplicitRhs := false) | return none
    applyCongrThm? mvarId congrThm

/--
Try to apply a `hcongr` congruence theorem, and then tries to close resulting goals
using `Eq.refl`, `HEq.refl`, and assumption.
-/
def MVarId.hcongr? (mvarId : MVarId) : MetaM (Option (List MVarId)) := do
  commitWhenSomeNoEx? do
    mvarId.checkNotAssigned `congr
    let mvarId ← mvarId.eqOfHEq
    mvarId.withContext do
      let target ← mvarId.getType'
      let some (_, lhs, _, _) := target.heq? | return none
      let lhs := lhs.cleanupAnnotations
      unless lhs.isApp do return none
      let congrThm ← mkHCongr lhs.getAppFn
      applyCongrThm? mvarId congrThm

/--
Try to apply `implies_congr`.
-/
def MVarId.congrImplies? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  observing? do
    let mvarId₁ :: mvarId₂ :: _ ← mvarId.apply (← mkConstWithFreshMVarLevels ``implies_congr) | throwError "unexpected number of goals"
    return [mvarId₁, mvarId₂]

/--
Given a goal of the form `⊢ f as = f bs`, `⊢ (p → q) = (p' → q')`, or `⊢ HEq (f as) (f bs)`, try to apply congruence.
It takes proof irrelevance into account, and the fact that `Decidable p` is a subsingleton.
-/
def MVarId.congrCore (mvarId : MVarId) : MetaM (List MVarId) := do
  if let some mvarIds ← mvarId.congr? then
    pure mvarIds
  else if let some mvarIds ← mvarId.hcongr? then
    pure mvarIds
  else if let some mvarIds ← mvarId.congrImplies? then
    pure mvarIds
  else
    throwTacticEx `congr mvarId "failed to apply congruence"

/--
Given a goal of the form `⊢ f as = f bs`, `⊢ (p → q) = (p' → q')`, or `⊢ HEq (f as) (f bs)`, try to apply congruence.
It takes proof irrelevance into account, and the fact that `Decidable p` is a subsingleton.

* Applies `congr` recursively up to depth `depth`.
* If `closePre := true`, it will attempt to close new goals
  using `Eq.refl`, `HEq.refl`, and `assumption` with reducible transparency.
* If `closePost := true`, it will try again on goals on which `congr` failed to make progress
  with default transparency.
-/
def MVarId.congrN (mvarId : MVarId) (depth : Nat := 1000000) (closePre := true) (closePost := true) : MetaM (List MVarId) := do
  let (_, s) ← go depth mvarId |>.run #[]
  return s.toList
where
  post (mvarId : MVarId) : StateRefT (Array MVarId) MetaM Unit := do
    if closePost && (← getTransparency) != .reducible then
      if let some mvarId ← mvarId.congrPre then
        modify (·.push mvarId)
    else
      modify (·.push mvarId)

  go (n : Nat) (mvarId : MVarId) : StateRefT (Array MVarId) MetaM Unit := do
    if let some mvarId ← if closePre then withReducible mvarId.congrPre else pure mvarId then
      match n with
      | 0 => post mvarId
      | n+1 =>
        let some mvarIds ← observing? (m := MetaM) mvarId.congrCore
          | post mvarId
        mvarIds.forM (go n)
