import Lean

/-!
# Ensure `replaceLocalDecl` instantiates metavariables

These tests ensure that `replaceLocalDecl` is aware of `FVarId`s present in the assignments of
metavariables present in the inserted declaration, and thus does not introduce unknown `FVarId`s by
inserting a local declaration before it's well-formed.

## Context

`replaceLocalDecl mvarId fvarId typeNew eqProof` replaces `fvarId` with a new FVarId that has the
same name but type `typeNew`. It does this by inserting a new local declaration with type `typeNew`
and clearing the old one if possible.

It makes sure that the new local declaration is inserted at the soonest point after `fvarId` at
which `typeNew` is well-formed. It does this by traversing `typeNew` and finding the `FVarId` with
the maximum index among all `FVarId`s occurring in `typeNew`.

If `replaceLocalDecl` encounters a metavariable during this traversal, it simply continues
traversing. Previously, it might have been the case that this metavariable we encountered was
assigned to an expression which contains an `FVarId` occurring after `fvarId`. This can lead to
`replaceLocalDecl` inserting a local declaration with a type which depends on `FVarId`s which come
after it in the local context, thus creating unknown `FVarId`s. (Note that the `FVarId`s of the
local declarations occurring after the insertion are modified, so the `FVarId` involved in the
assignment may not even exist in the local context anymore.)

We now attempt to prevent `replaceLocalDecl` from encountering assigned metavariables by
calling `instantiateMVars` in `replaceLocalDecl` before traversal.

Note that this is not a perfect solution to the overall problem; `Term.synthesizeSyntheticMVars`
may introduce assignments to inaccessible `FVarId`s after `replaceLocalDecl` has run, in which case
`instantiateMVars` is ineffective (as the metavariable has not even been assigned yet). See issue
#2727.
-/

/-! ## Direct test of instantiated mvars -/

open Lean Meta Elab Tactic in
/-- Replace the type of `fvar₁` with `fvar₂ = fvar₂` where the expression `fvar₂ = fvar₂` is hidden
under a metavariable assignment. Note that initially `fvar₁` must come before `fvar₂` in order to
make sure `replaceLocalDecl` is behaving correctly. -/
elab "replace " fvar₁:ident " with " fvar₂:ident " via " proof:term : tactic => withMainContext do
  let fvar₁ ← getFVarId fvar₁
  let fvar₂ ← getFVarId fvar₂
  let underlyingTypeNew ← inferType <|← mkEqRefl (Expr.fvar fvar₂)
  -- make a metavariable to use as the type in `replaceLocalDecl`; assign it to `underlyingTypeNew`
  let typeNewMVar ← mkFreshExprMVar none
  typeNewMVar.mvarId!.assign underlyingTypeNew
  let proof ← elabTerm proof underlyingTypeNew
  let { mvarId .. } ← (← getMainGoal).replaceLocalDecl fvar₁ typeNewMVar proof
  replaceMainGoal [mvarId]

example : True := by
  have h₁ : True := trivial
  have h₂ : Nat := 0
  replace h₁ with h₂ via eq_true rfl |>.symm
  /-
  Previously, goal state was:

  h₁: _uniq.NNNN = _uniq.NNNN
  h₂: Nat
  ⊢ True
  -/
