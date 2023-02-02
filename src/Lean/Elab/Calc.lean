/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.App

namespace Lean.Elab.Term
open Meta

/--
  Decompose `e` into `(r, a, b)`.

  Remark: it assumes the last two arguments are explicit. -/
def getCalcRelation? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) :=
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
  | _ => throwError "invalid 'calc' step, failed to synthesize `Trans` instance{indentExpr selfType}"

/--
Adds a type annotation to a hole that occurs immediately at the beginning of the term.
This is so that coercions can trigger when elaborating the term.
See https://github.com/leanprover/lean4/issues/2040 for futher rationale.

- `_ < 3` is annotated
- `(_) < 3` is not, because it occurs after an atom
- in `_ < _` only the first one is annotated
- `_ + 2 < 3` is annotated (not the best heuristic, ideally we'd like to annotate `_ + 2`)
- `lt _ 3` is not, because it occurs after an identifier
-/
partial def annotateFirstHoleWithType (t : Syntax) (type : Expr) : TermElabM Syntax :=
  -- The state is true if we should annotate the immediately next hole with the type.
  StateT.run' (go t) true
where
  go (t : Syntax) := do
    unless ← get do return t
    match t with
    | .node _ ``Lean.Parser.Term.hole _ =>
      set false
      `(($(⟨t⟩) : $(← exprToSyntax type)))
    | .node i k as => return .node i k (← as.mapM go)
    | _ => set false; return t

/--
  Elaborate `calc`-steps
-/
def elabCalcSteps (steps : Array Syntax) : TermElabM Expr := do
  let mut proofs := #[]
  let mut types  := #[]
  let mut prevRhs? := none
  for step in steps do
    let mut pred := step[0]
    if let some prevRhs := prevRhs? then
      pred ← annotateFirstHoleWithType pred (← inferType prevRhs)
    let type ← elabType pred
    let some (_, lhs, rhs) ← getCalcRelation? type |
      throwErrorAt step[0] "invalid 'calc' step, relation expected{indentExpr type}"
    if let some prevRhs := prevRhs? then
      unless (← isDefEqGuarded lhs prevRhs) do
        throwErrorAt step[0] "invalid 'calc' step, left-hand-side is{indentD m!"{lhs} : {← inferType lhs}"}\nprevious right-hand-side is{indentD m!"{prevRhs} : {← inferType prevRhs}"}"
    types := types.push type
    let proof ← elabTermEnsuringType step[2] type
    synthesizeSyntheticMVarsUsingDefault
    proofs := proofs.push proof
    prevRhs? := rhs
  let mut result := proofs[0]!
  let mut resultType := types[0]!
  for i in [1:proofs.size] do
    (result, resultType) ← withRef steps[i]![0] <| mkCalcTrans result resultType proofs[i]! types[i]!
  return result

/-- Elaborator for the `calc` term mode variant. -/
@[builtin_term_elab «calc»]
def elabCalc : TermElab :=  fun stx expectedType? => do
  let steps := #[stx[1]] ++ stx[2].getArgs
  let result ← elabCalcSteps steps
  ensureHasType expectedType? result
