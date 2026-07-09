/-
Copyright (c) 2026 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
import Lean.Elab.Tactic.Grind.Basic
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Replace
import Lean.Elab.SyntheticMVars
namespace Lean.Elab.Tactic.Grind
open Meta Grind

/--
Rewrites the target of the main goal using `term`, and re-establishes the `sym` invariants
(reducible constants unfolded, maximal sharing) on the resulting target.
Theorem premises that cannot be resolved by unification or type class resolution become
new goals.
-/
private def rwTarget (symm : Bool) (term : Syntax) : GrindTacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let mvarCounterSaved := (← getMCtx).mvarCounter
    let r ← Term.withSynthesize do
      let heq ← Term.elabTerm term none true
      if heq.hasSyntheticSorry then
        throwAbortTactic
      unless (← occursCheck goal.mvarId heq) do
        throwErrorAt term "Occurs check failed: Expression{indentExpr heq}\ncontains the goal {Expr.mvar goal.mvarId}"
      /-
      The target is in `sym` normal form (e.g., reducible constants have been unfolded), but the
      given equation is not. We unfold reducible constants in its statement so that `kabstract`
      key-matching can find occurrences of the lhs in the target, and the rhs requires less
      normalization after the rewrite.
      -/
      let heqType ← instantiateMVars (← inferType heq)
      let heqType' ← Sym.unfoldReducible heqType
      let heq ← if isSameExpr heqType heqType' then pure heq else mkExpectedTypeHint heq heqType'
      goal.mvarId.rewrite (← goal.mvarId.getType) heq symm
    let mctx ← getMCtx
    let mvarIds := r.mvarIds.filter fun mvarId => (mctx.getDecl mvarId |>.index) >= mvarCounterSaved
    let eNew ← liftSymM <| Sym.preprocessExpr r.eNew
    if eNew.hasExprMVar then
      throwError "`rw` failed, resulting target contains metavariables{indentExpr eNew}"
    let mvarId ← goal.mvarId.replaceTargetEq eNew r.eqProof
    let mvarIds ← mvarIds.filterM fun mvarId => return !(← mvarId.isAssigned)
    let sideGoals ← mvarIds.mapM fun mvarId => do
      let target ← mvarId.getType
      let target' ← liftSymM <| Sym.preprocessExpr target
      if isSameExpr target target' then
        -- The metavariable was created by `forallMetaTelescopeReducing` with kind `.natural`;
        -- prevent it from being assigned by unification in later steps.
        mvarId.setKind .syntheticOpaque
        return { goal with mvarId }
      else
        let mvarId ← mvarId.replaceTargetDefEq target'
        return { goal with mvarId }
    replaceMainGoal ({ goal with mvarId } :: sideGoals)

/--
Closes the main goal if its target is `True` or a reflexive `Eq`/`Iff`/`HEq`.
Since the target is maximally shared, reflexivity is detected using pointer equality.
-/
private def tryTrivialClose : GrindTacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.mvarId.getType
    if target.isTrue then
      goal.mvarId.assign (mkConst ``True.intro)
      replaceMainGoal []
      return ()
    let close (proof : Expr) : GrindTacticM Unit := do
      goal.mvarId.assign proof
      replaceMainGoal []
    match_expr target with
    | Eq α lhs rhs =>
      if isSameExpr lhs rhs then
        close <| mkApp2 (mkConst ``Eq.refl [← getLevel α]) α lhs
    | Iff lhs rhs =>
      if isSameExpr lhs rhs then
        close <| mkApp (mkConst ``Iff.refl) lhs
    | HEq α lhs β rhs =>
      if isSameExpr α β && isSameExpr lhs rhs then
        close <| mkApp2 (mkConst ``HEq.refl [← getLevel α]) α lhs
    | _ => return ()

@[builtin_grind_tactic Parser.Tactic.Grind.symRw] def evalSymRw : GrindTactic := fun stx => do
  ensureSym
  let `(grind| rw%$tk $s:rwRuleSeq) := stx | throwUnsupportedSyntax
  let lbrak := s.raw[0]
  let rules := s.raw[1]
  -- show initial state up to (incl.) `[`
  withTacticInfoContext (mkNullNode #[tk, lbrak]) (pure ())
  for rule in rules.getSepArgs do
    withTacticInfoContext rule do
      withRef rule do
        let symm := !rule[0].isNone
        let term := rule[1]
        rwTarget symm term
  tryTrivialClose

end Lean.Elab.Tactic.Grind
