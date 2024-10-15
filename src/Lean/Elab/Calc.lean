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

def getCalcFirstStep (step0 : TSyntax ``calcFirstStep) : TermElabM (TSyntax ``calcStep) :=
  withRef step0 do
  match step0  with
  | `(calcFirstStep| $term:term)      => `(calcStep| $term = _ := rfl)
  | `(calcFirstStep| $term := $proof) => `(calcStep| $term := $proof)
  | _ => throwUnsupportedSyntax

def getCalcSteps (steps : TSyntax ``calcSteps) : TermElabM (Array (TSyntax ``calcStep)) :=
  match steps with
  | `(calcSteps|
        $step0:calcFirstStep
        $rest*) => do
    let step0 ← getCalcFirstStep step0
    pure (#[step0] ++ rest)
  | _ => throwUnsupportedSyntax

def throwCalcRHSError (pred : Syntax) (rhs expectedRhs : Expr) : TermElabM α := do
  throwErrorAt pred "\
    invalid 'calc' step, right-hand-side is{indentD m!"{rhs} : {← inferType rhs}"}\n\
    but is expected to be{indentD m!"{expectedRhs} : {← inferType expectedRhs}"}"

def elabCalcSteps (steps : TSyntax ``calcSteps) (expectedLhs? : Option Expr := none) (expectedRhs? : Option Expr := none) :
    TermElabM (Expr × Expr) := do
  let mut result? := none
  let mut prevRhs? := expectedLhs?
  let steps ← getCalcSteps steps
  for h : i in [0:steps.size] do
    let step := steps[i]
    let `(calcStep| $pred := $proofTerm) := step | throwUnsupportedSyntax
    let type ← elabType <| ← do
      if let some prevRhs := prevRhs? then
        annotateFirstHoleWithType pred (← inferType prevRhs)
      else
        pure pred
    let some (_, lhs, rhs) ← getCalcRelation? type |
      throwErrorAt pred "invalid 'calc' step, relation expected{indentExpr type}"
    if let some prevRhs := prevRhs? then
      unless (← isDefEqGuarded lhs prevRhs) do
        if i == 0 then
          throwErrorAt pred "\
            invalid 'calc' step, left-hand-side is{indentD m!"{lhs} : {← inferType lhs}"}\n\
            but is expected to be{indentD m!"{prevRhs} : {← inferType prevRhs}"}"
        else
          throwErrorAt pred "\
            invalid 'calc' step, left-hand-side is{indentD m!"{lhs} : {← inferType lhs}"}\n\
            but previous right-hand-side is{indentD m!"{prevRhs} : {← inferType prevRhs}"}"
    if i + 1 == steps.size then
      if let some eRhs := expectedRhs? then
        unless (← isDefEqGuarded rhs eRhs) do
          throwCalcRHSError pred rhs eRhs
    let proof ← withFreshMacroScope do elabTermEnsuringType proofTerm type
    result? := some <| ← do
      if let some (result, resultType) := result? then
        synthesizeSyntheticMVarsUsingDefault
        withRef pred do mkCalcTrans result resultType proof type
      else
        pure (proof, type)
    prevRhs? := rhs
  synthesizeSyntheticMVarsUsingDefault
  return result?.get!

private def tryPostponeIfNotRelation? (expectedType? : Option Expr) : TermElabM (Option (Expr × Expr × Expr)) := do
  let some expectedType := expectedType? | return none
  let expectedType := (← instantiateMVars expectedType).consumeMData
  if let some data@(r, _, _) ← Term.getCalcRelation? expectedType then
    unless (← isMVarApp r) do
      return data
  tryPostpone
  return none

/--
Throw an error that the relations are not defeq. Assumes that `r` and `er` have the same type.
This creates an error message that shows `_ < _` vs `_ ≤ _` for example.
-/
def throwCalcRelationError (r er : Expr) : TermElabM α := do
  forallBoundedTelescope (← inferType r) (some 2) fun args _ => do
    let args := args.map fun arg => arg.setOption `pp.analysis.hole true
    let (er', r') ← addPPExplicitToExposeDiff (mkAppN er args) (mkAppN r args)
    throwError "\
      'calc' expression has the relation\
      {indentD r'}\n\
      but is expected to have the relation\
      {indentD er'}"

/-- Elaborator for the `calc` term mode variant. -/
@[builtin_term_elab Lean.calc]
def elabCalc : TermElab
  | `(calc%$tk $steps:calcSteps), expectedType? => withRef tk do
    let (er?, elhs?, erhs?) :=
      if let some (er, elhs, erhs) := ← tryPostponeIfNotRelation? expectedType? then
        (some er, some elhs, some erhs)
      else
        (none, none, none)
--    logInfo m!"er{indentD er?}\nelhs{indentD elhs?}\nerhs{indentD erhs?}"
    let (result, resultType) ← elabCalcSteps steps (expectedLhs? := elhs?) (expectedRhs? := erhs?)
    if let some er := er? then
      let some (r, _, _) ← getCalcRelation? resultType | unreachable!
      -- At this point we know the lhs's and rhs's match up. All that is left is checking the relations are the same.
      unless (← isDefEqGuarded r er) do
        throwCalcRelationError r er
    return result
  | _, _ => throwUnsupportedSyntax

end Lean.Elab.Term
