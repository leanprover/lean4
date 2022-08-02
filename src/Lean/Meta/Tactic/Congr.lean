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
It also tries to apply `heq_of_eq`, and clears `fvarId`.
-/
private def congrPost (fvarId : FVarId) (mvarIds : List MVarId) : MetaM (List MVarId) :=
  mvarIds.filterMapM fun mvarId => do
    let mvarId ← mvarId.heqOfEq
    try mvarId.refl; return none catch _ => pure ()
    try mvarId.hrefl; return none catch _ => pure ()
    if (← mvarId.assumptionCore) then return none
    let mvarId ← mvarId.tryClear fvarId
    return some mvarId

/--
Asserts the given congruence theorem as fresh hypothesis, and then applies it.
Return the `fvarId` for the new hypothesis and the new subgoals.
-/
private def applyCongrThm? (mvarId : MVarId) (congrThm : CongrTheorem) : MetaM (Option (FVarId × List MVarId)) := do
  let mvarId ← mvarId.assert (← mkFreshUserName `h_congr_thm) congrThm.type congrThm.proof
  let (fvarId, mvarId) ← mvarId.intro1P
  let mvarIds ← mvarId.apply (mkFVar fvarId)
  return some (fvarId, mvarIds)

/--
Try to apply a `simp` congruence theorem.
-/
def MVarId.congr? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `congr
    let target ← mvarId.getType'
    let some (_, lhs, _) := target.eq? | return none
    unless lhs.isApp do return none
    let some congrThm ← mkCongrSimp? lhs.getAppFn | return none
    let some (fvarId, mvarIds) ← applyCongrThm? mvarId congrThm | return none
    congrPost fvarId mvarIds

/--
Try to apply a hcongr congruence theorem. This kind of theorem is used by
the congruence closure module.
-/
def MVarId.hcongr? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `congr
    let target ← mvarId.getType'
    let some (_, lhs, _, _) := target.heq? | return none
    unless lhs.isApp do return none
    let congrThm ← mkHCongr lhs.getAppFn
    trace[Meta.debug] "congrThm: {congrThm.type}"
    let some (fvarId, mvarIds) ← applyCongrThm? mvarId congrThm | return none
    congrPost fvarId mvarIds

/--
Given a goal of the form `⊢ f as = f bs` or `⊢ HEq (f as) (f bs)`, try to apply congruence.
It takes proof irrelevance into account, the fact that `Decidable p` is a subsingleton.
It tries to close new subgoals using `Eq.refl`, `HEq.refl`, and `assumption`.
-/
def MVarId.congr (mvarId : MVarId) : MetaM (List MVarId) := do
  if let some mvarIds ← mvarId.congr? then
    return mvarIds
  else if let some mvarIds ← mvarId.hcongr? then
    return mvarIds
  else
    throwTacticEx `congr mvarId "failed to apply congruence"

/--
Applies `congr` recursively up to depth `n`.
-/
def MVarId.congrN (mvarId : MVarId) (n : Nat) : MetaM (List MVarId) := do
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

