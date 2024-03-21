/-
Copyright (c) 2022 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen, Thomas Murrills
-/
prelude
import Lean.Meta.Tactic.Apply
import Lean.Elab.Tactic.Basic

/-!
# `rfl` tactic extension for reflexive relations

This extends the `rfl` tactic so that it works on any reflexive relation,
provided the reflexivity lemma has been marked as `@[refl]`.
-/

namespace Lean.Meta.Rfl

open Lean Meta

/-- Discrimation tree settings for the `refl` extension. -/
def reflExt.config : WhnfCoreConfig := {}

/-- Environment extensions for `refl` lemmas -/
initialize reflExt :
    SimpleScopedEnvExtension (Name × Array DiscrTree.Key) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt (n, ks) => dt.insertCore ks n
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `refl
  descr := "reflexivity relation"
  add := fun decl _ kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let (_, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
    let fail := throwError
      "@[refl] attribute only applies to lemmas proving x ∼ x, got {declTy}"
    let .app (.app rel lhs) rhs := targetTy | fail
    unless ← withNewMCtxDepth <| isDefEq lhs rhs do fail
    let key ← DiscrTree.mkPath rel reflExt.config
    reflExt.add (decl, key) kind
}

open Elab Tactic

/-- `MetaM` version of the `rfl` tactic.

This tactic applies to a goal whose target has the form `x ~ x`, where `~` is a reflexive
relation, that is, a relation which has a reflexive lemma tagged with the attribute [refl].
-/
def _root_.Lean.MVarId.applyRfl (goal : MVarId) : MetaM Unit := do
  let .app (.app rel _) _ ← whnfR <|← instantiateMVars <|← goal.getType
    | throwError "reflexivity lemmas only apply to binary relations, not{
        indentExpr (← goal.getType)}"
  let s ← saveState
  let mut ex? := none
  for lem in ← (reflExt.getState (← getEnv)).getMatch rel reflExt.config do
    try
      let gs ← goal.apply (← mkConstWithFreshMVarLevels lem)
      if gs.isEmpty then return () else
        logError <| MessageData.tagged `Tactic.unsolvedGoals <| m!"unsolved goals\n{
          goalsToMessageData gs}"
    catch e =>
      ex? := ex? <|> (some (← saveState, e)) -- stash the first failure of `apply`
    s.restore
  if let some (sErr, e) := ex? then
    sErr.restore
    throw e
  else
    throwError "rfl failed, no lemma with @[refl] applies"

/-- Helper theorem for `Lean.MVarId.liftReflToEq`. -/
private theorem rel_of_eq_and_refl {α : Sort _} {R : α → α → Prop}
    {x y : α} (hxy : x = y) (h : R x x) : R x y :=
  hxy ▸ h

/--
Convert a goal of the form `x ~ y` into the form `x = y`, where `~` is a reflexive
relation, that is, a relation which has a reflexive lemma tagged with the attribute `[refl]`.
If this can't be done, returns the original `MVarId`.
-/
def _root_.Lean.MVarId.liftReflToEq (mvarId : MVarId) : MetaM MVarId := do
  mvarId.checkNotAssigned `liftReflToEq
  let .app (.app rel _) _ ← withReducible mvarId.getType' | return mvarId
  if rel.isAppOf `Eq then
    -- No need to lift Eq to Eq
    return mvarId
  for lem in ← (reflExt.getState (← getEnv)).getMatch rel reflExt.config do
    let res ← observing? do
      -- First create an equality relating the LHS and RHS
      -- and reduce the goal to proving that LHS is related to LHS.
      let [mvarIdEq, mvarIdR] ← mvarId.apply (← mkConstWithFreshMVarLevels ``rel_of_eq_and_refl)
        | failure
      -- Then fill in the proof of the latter by reflexivity.
      let [] ← mvarIdR.apply (← mkConstWithFreshMVarLevels lem) | failure
      return mvarIdEq
    if let some mvarIdEq := res then
      return mvarIdEq
  return mvarId

end Lean.Meta.Rfl
