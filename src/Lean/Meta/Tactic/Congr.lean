/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.CongrTheorems
import Lean.Meta.Tactic.Assert
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Assumption

namespace Lean
open Meta

/--
Postprocessor after applying congruence theorem.
Tries to close new goals using `Eq.refl`, `HEq.refl`, and `assumption`.
It also tries to apply `heq_of_eq`.
-/
private def congrPost (mvarIds : List MVarId) : MetaM (List MVarId) :=
  mvarIds.filterMapM fun mvarId => do
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
  let mvarIds ← mvarId.apply (mkFVar fvarId)
  mvarIds.mapM fun mvarId => mvarId.tryClear fvarId

/--
Try to apply a `simp` congruence theorem.
-/
def MVarId.congr? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  mvarId.withContext do
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
def MVarId.hcongr? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `congr
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
It takes proof irrelevance into account, the fact that `Decidable p` is a subsingleton.
If `closeEasy := true`, it tries to close new subgoals using `Eq.refl`, `HEq.refl`, and `assumption`.
-/
def MVarId.congr (mvarId : MVarId) (closeEasy := true) : MetaM (List MVarId) := do
  let mvarIds ← if let some mvarIds ← mvarId.congr? then
    pure mvarIds
  else if let some mvarIds ← mvarId.hcongr? then
    pure mvarIds
  else if let some mvarIds ← mvarId.congrImplies? then
    pure mvarIds
  else
    throwTacticEx `congr mvarId "failed to apply congruence"
  if closeEasy then
    congrPost mvarIds
  else
    return mvarIds

/--
Applies `congr` recursively up to depth `n`.
-/
def MVarId.congrN (mvarId : MVarId) (n : Nat) : MetaM (List MVarId) := do
  if n == 1 then
    mvarId.congr
  else
    let (_, s) ← go n mvarId |>.run #[]
    return s.toList
where
  go (n : Nat) (mvarId : MVarId) : StateRefT (Array MVarId) MetaM Unit := do
    match n with
    | 0 => modify (·.push mvarId)
    | n+1 =>
      let some mvarIds ← observing? (m := MetaM) mvarId.congr
        | modify (·.push mvarId)
      mvarIds.forM (go n)
end Lean
