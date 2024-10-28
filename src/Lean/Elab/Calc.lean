/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.App

namespace Lean.Elab.Term
open Meta

/--
Decompose `e` into `(r, a, b)`.

Remark: it assumes the last two arguments are explicit.
-/
def getCalcRelation? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  if e.getAppNumArgs < 2 then
    return none
  else
    return some (e.appFn!.appFn!, e.appFn!.appArg!, e.appArg!)

private def getRelUniv (r : Expr) : MetaM Level := do
  let rType ← inferType r
  forallTelescopeReducing rType fun _ sort => do
    let .sort u ← whnf sort | throwError "unexpected relation type{indentExpr rType}"
    return u

def mkCalcTrans (result resultType step stepType : Expr) : MetaM (Expr × Expr) := do
  let some (r, a, b) ← getCalcRelation? resultType | unreachable!
  let some (s, _, c) ← getCalcRelation? (← instantiateMVars stepType) | unreachable!
  let u ← getRelUniv r
  let v ← getRelUniv s
  let (α, β, γ)       := (← inferType a, ← inferType b, ← inferType c)
  let (u_1, u_2, u_3) := (← getLevel α, ← getLevel β, ← getLevel γ)
  let w ← mkFreshLevelMVar
  let t ← mkFreshExprMVar (← mkArrow α (← mkArrow γ (mkSort w)))
  let selfType := mkAppN (Lean.mkConst ``Trans [u, v, w, u_1, u_2, u_3]) #[α, β, γ, r, s, t]
  match (← trySynthInstance selfType) with
  | .some self =>
    let result := mkAppN (Lean.mkConst ``Trans.trans [u, v, w, u_1, u_2, u_3]) #[α, β, γ, r, s, t, self, a, b, c, result, step]
    let resultType := (← instantiateMVars (← inferType result)).headBeta
    unless (← getCalcRelation? resultType).isSome do
      throwError "invalid 'calc' step, step result is not a relation{indentExpr resultType}"
    return (result, resultType)
  | _ => throwError "invalid 'calc' step, failed to synthesize `Trans` instance{indentExpr selfType}{useDiagnosticMsg}"

/--
Adds a type annotation to a hole that occurs immediately at the beginning of the term.
This is so that coercions can trigger when elaborating the term.
See https://github.com/leanprover/lean4/issues/2040 for further rationale.

- `_ < 3` is annotated
- `(_) < 3` is not, because it occurs after an atom
- in `_ < _` only the first one is annotated
- `_ + 2 < 3` is annotated (not the best heuristic, ideally we'd like to annotate `_ + 2`)
- `lt _ 3` is not, because it occurs after an identifier
-/
partial def annotateFirstHoleWithType (t : Term) (type : Expr) : TermElabM Term :=
  -- The state is true if we should annotate the immediately next hole with the type.
  return ⟨← StateT.run' (go t) true⟩
where
  go (t : Syntax) := do
    unless ← get do return t
    match t with
    | .node _ ``Lean.Parser.Term.hole _ =>
      set false
      `(($(⟨t⟩) : $(← exprToSyntax type)))
    | .node i k as => return .node i k (← as.mapM go)
    | _ => set false; return t

/-- View of a `calcStep`. -/
structure CalcStepView where
  ref : Syntax
  /-- A relation term like `a ≤ b` -/
  term : Term
  /-- A proof of `term` -/
  proof : Term
  deriving Inhabited

def mkCalcFirstStepView (step0 : TSyntax ``calcFirstStep) : TermElabM CalcStepView :=
  withRef step0 do
  match step0  with
  | `(calcFirstStep| $term:term)      => return { ref := step0, term := ← `($term = _), proof := ← ``(rfl)}
  | `(calcFirstStep| $term := $proof) => return { ref := step0, term, proof}
  | _ => throwUnsupportedSyntax

def mkCalcStepViews (steps : TSyntax ``calcSteps) : TermElabM (Array CalcStepView) :=
  match steps with
  | `(calcSteps|
        $step0:calcFirstStep
        $rest*) => do
    let mut steps := #[← mkCalcFirstStepView step0]
    for step in rest do
      let `(calcStep| $term := $proof) := step | throwUnsupportedSyntax
      steps := steps.push { ref := step, term, proof }
    return steps
  | _ => throwUnsupportedSyntax

def elabCalcSteps (steps : Array CalcStepView) : TermElabM (Expr × Expr) := do
  let mut result? := none
  let mut prevRhs? := none
  for step in steps do
    let type ← elabType <| ← do
      if let some prevRhs := prevRhs? then
        annotateFirstHoleWithType step.term (← inferType prevRhs)
      else
        pure step.term
    let some (_, lhs, rhs) ← getCalcRelation? type |
      throwErrorAt step.term "invalid 'calc' step, relation expected{indentExpr type}"
    if let some prevRhs := prevRhs? then
      unless (← isDefEqGuarded lhs prevRhs) do
        throwErrorAt step.term "\
          invalid 'calc' step, left-hand side is{indentD m!"{lhs} : {← inferType lhs}"}\n\
          but previous right-hand side is{indentD m!"{prevRhs} : {← inferType prevRhs}"}"
    let proof ← withFreshMacroScope do elabTermEnsuringType step.proof type
    result? := some <| ← do
      if let some (result, resultType) := result? then
        synthesizeSyntheticMVarsUsingDefault
        withRef step.term do mkCalcTrans result resultType proof type
      else
        pure (proof, type)
    prevRhs? := rhs
  synthesizeSyntheticMVarsUsingDefault
  return result?.get!

def throwCalcFailure (steps : Array CalcStepView) (expectedType result : Expr) : MetaM α := do
  let resultType := (← instantiateMVars (← inferType result)).headBeta
  let some (r, lhs, rhs) ← getCalcRelation? resultType | unreachable!
  if let some (er, elhs, erhs) ← getCalcRelation? expectedType then
    if ← isDefEqGuarded r er then
      let mut failed := false
      unless ← isDefEqGuarded lhs elhs do
        logErrorAt steps[0]!.term m!"\
          invalid 'calc' step, left-hand side is{indentD m!"{lhs} : {← inferType lhs}"}\n\
          but is expected to be{indentD m!"{elhs} : {← inferType elhs}"}"
        failed := true
      unless ← isDefEqGuarded rhs erhs do
        logErrorAt steps.back.term m!"\
          invalid 'calc' step, right-hand side is{indentD m!"{rhs} : {← inferType rhs}"}\n\
          but is expected to be{indentD m!"{erhs} : {← inferType erhs}"}"
        failed := true
      if failed then
        throwAbortTerm
  throwTypeMismatchError "'calc' expression" expectedType resultType result

/-!
Warning! It is *very* tempting to try to improve `calc` so that it makes use of the expected type
to unify with the LHS and RHS.
Two people have already re-implemented `elabCalcSteps` trying to do so and then reverted the changes,
not being aware of examples like https://github.com/leanprover/lean4/issues/2073

The problem is that the expected type might need to be unfolded to get an accurate LHS and RHS.
(Consider `≤` vs `≥`. Users expect to be able to use `calc` to prove `≥` using chained `≤`!)
Furthermore, the types of the LHS and RHS do not need to be the same (consider `x ∈ S` as a relation),
so we also cannot use the expected LHS and RHS as type hints.
-/

/-- Elaborator for the `calc` term mode variant. -/
@[builtin_term_elab Lean.calc]
def elabCalc : TermElab
  | `(calc%$tk $steps:calcSteps), expectedType? => withRef tk do
    let steps ← mkCalcStepViews steps
    let (result, _) ← elabCalcSteps steps
    ensureHasTypeWithErrorMsgs expectedType? result
      (mkImmedErrorMsg := fun _ => throwCalcFailure steps)
      (mkErrorMsg := fun _ => throwCalcFailure steps)
  | _, _ => throwUnsupportedSyntax

end Lean.Elab.Term
