/-
Copyright (c) 2022 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Mario Carneiro, Kim Morrison
-/
module
prelude
public import Lean.Meta.Reduce
public import Lean.Meta.Tactic.Assert
public import Lean.Meta.DiscrTree.Main
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic.Apply
import Lean.Elab.Tactic.Basic
public section

/-!
# `symm` tactic

This implements the `symm` tactic, which can apply symmetry theorems to either the goal or a
hypothesis.
-/

open Lean Meta

namespace Lean.Meta.Symm

/-- Environment extensions for symm lemmas -/
builtin_initialize symmExt :
    SimpleScopedEnvExtension (Name × Array DiscrTree.Key) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt (n, ks) => dt.insertKeyValue ks n
    initial := {}
  }

/--
Tags symmetry lemmas to be used by the `symm` tactic.

A symmetry lemma should be of the form `r x y → r y x` where `r` is an arbitrary relation.
-/
@[builtin_doc]
builtin_initialize registerBuiltinAttribute {
  name := `symm
  descr := "symmetric relation"
  add := fun decl _ kind => MetaM.run' do
    let declTy ← inferType (← mkConstWithFreshMVarLevels decl)
    let (_, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
    let fail := throwError
      "@[symm] attribute only applies to lemmas proving x ∼ y → y ∼ x, got {declTy}"
    -- Note: this checks that `targetTy` has at least two arguments.
    -- There's no guarantee that the last two arguments are the arguments to the relation!
    -- Possibly there are instance arguments after the main arguments. This is an approximation.
    let .app (.app rel _) _ ← whnfR targetTy | fail
    -- Instantiate another copy, then try unifying its last argument with the target.
    let declTy' ← inferType (← mkConstWithFreshMVarLevels decl)
    let (xs', _, _) ← withReducible <| forallMetaTelescopeReducing declTy'
    let some h := xs'.back? | fail
    unless ← withoutModifyingMCtx (do isDefEq targetTy (← inferType h)) do fail
    let key ← DiscrTree.mkPath rel
    symmExt.add (decl, key) kind
}

/-- Return the symmetry lemmas that match the target type. -/
def getSymmLems (tgt : Expr) : MetaM (Expr × Array Name) := do
  let .app (.app rel _) _ := tgt
    | throwError "Symmetry lemmas only apply to binary relations, not{indentExpr tgt}"
  return (rel, ← (symmExt.getState (← getEnv)).getMatch rel)

def forEachSymmLemma {α} (g? : Option MVarId) (tgt : Expr)
    (k : Expr → Expr → Array Expr → Expr → Expr → MetaM α) : MetaM α := do
  let tgt ← instantiateMVars (← whnfR tgt)
  let (rel, lems) ← getSymmLems tgt
  let s ← saveState
  let mut ex? := none
  for lem in lems do
    try
      let lem ← mkConstWithFreshMVarLevels lem
      let (args, bis, body) ← withReducible <| forallMetaTelescopeReducing (← inferType lem)
      let some eArg := args.back? | panic! "invalid symm lemma"
      let res ← k lem tgt args body eArg
      synthAppInstances `symm g? args.pop bis.pop (allowSynthFailures := false) (synthAssignedInstances := true)
      let gs ← args.pop.filterM fun arg => not <$> arg.mvarId!.isAssigned
      unless gs.isEmpty do
        throwError MessageData.tagged `Tactic.unsolvedGoals <| m!"unsolved goals\n{Elab.goalsToMessageData (gs.map Expr.mvarId!).toList}"
      return res
    catch e =>
      unless ex?.isSome do
        ex? := some (← saveState, e)
    s.restore
  if let some (sErr, e) := ex? then
    sErr.restore
    throw e
  else
    throwTacticEx `symm g? <|  m!"No `[symm]` lemma registered for relation{indentExpr rel}"
      ++ MessageData.hint' m!"Add the `[symm]` attribute to symmetry lemmas for{inlineExpr rel}to use this tactic"

end Lean.Meta.Symm

open Lean.Meta.Symm

namespace Lean.Expr

/--
Given a term `e : a ~ b`, constructs a term in `b ~ a` using `@[symm]` lemmas.

The `g?` argument is used only for error reporting.
-/
def applySymm (g? : Option MVarId) (e : Expr) : MetaM Expr := do
  forEachSymmLemma g? (← inferType e) fun lem tgt args body eArg => do
    unless ← isDefEq eArg e do
      let eArgTy ← instantiateMVars (← whnfR (← inferType eArg))
      throwError MessageData.ofLazyM (es := #[eArgTy, tgt]) do
        let (eArgTy, tgt) ← addPPExplicitToExposeDiff eArgTy tgt
        return m!"The last hypothesis{indentExpr eArgTy}\nof the symmetry lemma is not definitionally equal to{indentExpr tgt}"
    return ← mkExpectedTypeHint (mkAppN lem args) (← instantiateMVars body)

end Lean.Expr

namespace Lean.MVarId

/--
Apply a symmetry lemma (i.e. marked with `@[symm]`) to a metavariable.

The type of `g` should be of the form `a ~ b`, and is used to index the symm lemmas.
-/
def applySymm (g : MVarId) : MetaM MVarId := do
  forEachSymmLemma g (← g.getType) fun lem tgt args body eArg => do
    unless ← isDefEq tgt body do
      throwError MessageData.ofLazyM (es := #[tgt, body]) do
        let (tgt, body) ← addPPExplicitToExposeDiff tgt body
        return m!"The conclusion{indentExpr body}\nof the symmetry lemma is not definitionally equal to the goal{indentExpr tgt}"
    g.assign (mkAppN lem args)
    let g' := eArg.mvarId!
    g'.setTag (← g.getTag)
    g.setKind .syntheticOpaque
    return g'

/-- Use a symmetry lemma (i.e. marked with `@[symm]`) to replace a hypothesis in a goal. -/
def applySymmAt (h : FVarId) (g : MVarId) : MetaM MVarId := do
  let h' ← g.withContext <| (Expr.fvar h).applySymm g
  pure (← g.replace h h').mvarId

/-- For every hypothesis `h : a ~ b` where a `@[symm]` lemma is available,
add a hypothesis `h_symm : b ~ a`. -/
def symmSaturate (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g' := g
  let hyps ← getLocalHyps
  let types ← hyps.mapM inferType
  for h in hyps do try
    let symm ← h.applySymm g
    let symmType ← inferType symm
    if ¬ (← types.anyM (isDefEq symmType)) then
      (_, g') ← g'.note ((← h.fvarId!.getUserName).appendAfter "_symm") symm
  catch _ => g' ← pure g'
  return g'

end Lean.MVarId
