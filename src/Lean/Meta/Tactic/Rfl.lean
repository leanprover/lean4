/-
Copyright (c) 2022 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen, Thomas Murrills, Joachim Breitner
-/
prelude
import Lean.Meta.Tactic.Apply
import Lean.Elab.Tactic.Basic
import Lean.Meta.Tactic.Refl

/-!
# `rfl` tactic extension for reflexive relations

This extends the `rfl` tactic so that it works on any reflexive relation,
provided the reflexivity lemma has been marked as `@[refl]`.
-/

namespace Lean.Meta.Rfl

open Lean Meta

/-- Environment extensions for `refl` lemmas -/
initialize reflExt :
    SimpleScopedEnvExtension (Name × Array DiscrTree.Key) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt (n, ks) => dt.insertCore ks n
    initial := {}
  }

/--
Tags reflexivity lemmas to be used by the `rfl` tactic.

A reflexivity lemma should have the conclusion `r x x` where `r` is an arbitrary relation.

It is not possible to tag reflexivity lemmas for `=` using this attribute. These are handled as a
special case in the `rfl` tactic.
-/
@[builtin_doc]
builtin_initialize registerBuiltinAttribute {
  name := `refl
  descr := "reflexivity relation"
  add := fun decl _ kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let (_, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
    let fail := throwError
      "@[refl] attribute only applies to lemmas proving x ∼ x, got {declTy}"
    let .app (.app rel lhs) rhs := targetTy | fail
    if let .app (.const ``Eq [_]) _ := rel then
      throwError "@[refl] attribute may not be used on `Eq.refl`."
    unless ← withNewMCtxDepth <| isDefEq lhs rhs do fail
    let key ← DiscrTree.mkPath rel
    reflExt.add (decl, key) kind
}

open Elab Tactic

/-- `MetaM` version of the `rfl` tactic.

This tactic applies to a goal whose target has the form `x ~ x`, where `~` is a reflexive
relation, that is, equality or another relation which has a reflexive lemma tagged with the
attribute [refl].
-/
def _root_.Lean.MVarId.applyRfl (goal : MVarId) : MetaM Unit := goal.withContext do
  -- NB: uses whnfR, we do not want to unfold the relation itself
  let t ← whnfR <|← instantiateMVars <|← goal.getType
  if t.getAppNumArgs < 2 then
    throwTacticEx `rfl goal "expected goal to be a binary relation"

  -- Special case HEq here as it has a different argument order.
  if t.isAppOfArity ``HEq 4 then
    let gs ← goal.applyConst ``HEq.refl
    unless gs.isEmpty do
      throwTacticEx `rfl goal <| MessageData.tagged `Tactic.unsolvedGoals <| m!"unsolved goals\n{
        goalsToMessageData gs}"
    return

  let rel := t.appFn!.appFn!
  let lhs := t.appFn!.appArg!
  let rhs := t.appArg!

  let success ← approxDefEq <| isDefEqGuarded lhs rhs
  unless success do
    let explanation := MessageData.ofLazyM (es := #[lhs, rhs]) do
      let (lhs, rhs) ← addPPExplicitToExposeDiff lhs rhs
      return m!"the left-hand side{indentExpr lhs}\nis not definitionally equal to the right-hand side{indentExpr rhs}"
    throwTacticEx `rfl goal explanation

  if rel.isAppOfArity `Eq 1 then
    -- The common case is equality: just use `Eq.refl`
    let us := rel.appFn!.constLevels!
    let α :=  rel.appArg!
    goal.assign (mkApp2 (mkConst ``Eq.refl us) α lhs)
  else
    -- Else search through `@refl` keyed by the relation
    -- We change the type to `lhs ~ lhs` so that we don't do the (possibly costly) `lhs =?= rhs`
    -- check again.
    goal.setType (.app t.appFn! lhs)
    let s ← saveState
    let mut ex? := none
    for lem in ← (reflExt.getState (← getEnv)).getMatch rel do
      try
        let gs ← goal.apply (← mkConstWithFreshMVarLevels lem) (term? := m!"'{.ofConstName lem}'")
        if gs.isEmpty then return () else
          throwError MessageData.tagged `Tactic.unsolvedGoals <| m!"unsolved goals\n{
            goalsToMessageData gs}"
      catch e =>
        unless ex?.isSome do
          ex? := some (← saveState, e) -- stash the first failure of `apply`
      s.restore
    if let some (sErr, e) := ex? then
      sErr.restore
      throw e
    else
      throwTacticEx `rfl goal m!"no @[refl] lemma registered for relation{indentExpr rel}"

/-- Helper theorem for `Lean.MVarId.liftReflToEq`. -/
private theorem rel_of_eq_and_refl {α : Sort _} {R : α → α → Prop}
    {x y : α} (hxy : x = y) (h : R x x) : R x y :=
  hxy ▸ h

/--
Convert a goal of the form `x ~ y` into the form `x = y`, where `~` is a reflexive
relation, that is, a relation which has a reflexive lemma tagged with the attribute `@[refl]`.
If this can't be done, returns the original `MVarId`.
-/
def _root_.Lean.MVarId.liftReflToEq (mvarId : MVarId) : MetaM MVarId := do
  mvarId.checkNotAssigned `liftReflToEq
  let .app (.app rel _) _ ← withReducible mvarId.getType' | return mvarId
  if rel.isAppOf `Eq then
    -- No need to lift Eq to Eq
    return mvarId
  for lem in ← (reflExt.getState (← getEnv)).getMatch rel do
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
