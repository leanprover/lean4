/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module
prelude
public import Lean.Meta.Basic
import Lean.Meta.Tactic.Delta
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Constructions.SparseCasesOn
import Lean.Meta.Constructions.SparseCasesOnEq
import Lean.Meta.HasNotBit
import Lean.Meta.Tactic.Cases

namespace Lean.Meta

private def rewriteGoalUsingEq (goal : MVarId) (eq : Expr) (symm : Bool := false) : MetaM MVarId := do
  let rewriteResult ← goal.rewrite (←goal.getType) eq symm
  goal.replaceTargetEq rewriteResult.eNew rewriteResult.eqProof

/--
Reduces a sparse casesOn applied to a concrete constructor.
-/
public def reduceSparseCasesOn (mvarId : MVarId) : MetaM (Array MVarId) := do
  let some (_, lhs) ← matchEqHEqLHS? (← mvarId.getType) | throwError "Target not an equality"
  lhs.withApp fun f xs => do
  let .const matchDeclName _  := f | throwError "Not a const application"
  let some sparseCasesOnInfo ← getSparseCasesOnInfo matchDeclName | throwError "Not a sparse casesOn application"
  withTraceNode `Meta.Match.matchEqs (msg := (return m!"{exceptEmoji ·} splitSparseCasesOn")) do
  if xs.size < sparseCasesOnInfo.arity then
    throwError "Not enough arguments for sparse casesOn application"
  let majorIdx := sparseCasesOnInfo.majorPos
  let major := xs[majorIdx]!
  let some ctorInfo  ← isConstructorApp'? major
    | throwError "Major premise is not a constructor application:{indentExpr major}"
  if sparseCasesOnInfo.insterestingCtors.contains ctorInfo.name then
    let mvarId' ← mvarId.modifyTargetEqLHS fun lhs =>
      unfoldDefinition lhs
    return #[mvarId']
  else
    let sparseCasesOnEqName ← getSparseCasesOnEq matchDeclName
    let eqProof := mkConst sparseCasesOnEqName lhs.getAppFn.constLevels!
    let eqProof := mkAppN eqProof lhs.getAppArgs[:sparseCasesOnInfo.arity]
    let eqProof := mkApp eqProof (← mkHasNotBitProof (mkRawNatLit ctorInfo.cidx) (←  sparseCasesOnInfo.insterestingCtors.mapM (fun n => return (← getConstInfoCtor n).cidx)))
    let mvarId' ← rewriteGoalUsingEq mvarId eqProof
    return #[mvarId']

public def splitSparseCasesOn (mvarId : MVarId) : MetaM (Array MVarId) := do
  let some (_, lhs) ← matchEqHEqLHS? (← mvarId.getType) | throwError "Target not an equality"
  lhs.withApp fun f xs => do
  let .const matchDeclName _  := f | throwError "Not a const application"
  let some sparseCasesOnInfo ← getSparseCasesOnInfo matchDeclName | throwError "Not a sparse casesOn application"
  withTraceNode `Meta.Match.matchEqs (msg := (return m!"{exceptEmoji ·} splitSparseCasesOn")) do
  try
    trace[Meta.Match.matchEqs] "splitSparseCasesOn running on\n{mvarId}"
    if xs.size < sparseCasesOnInfo.arity then
      throwError "Not enough arguments for sparse casesOn application"
    let majorIdx := sparseCasesOnInfo.majorPos
    unless xs[majorIdx]!.isFVar do
      throwError "Major premise is not a free variable:{indentExpr xs[majorIdx]!}"
    let fvarId := xs[majorIdx]!.fvarId!
    let subgoals ← mvarId.cases fvarId (interestingCtors? := sparseCasesOnInfo.insterestingCtors)
    subgoals.mapM fun s => s.mvarId.withContext do
      if s.ctorName.isNone then
        unless s.fields.size = 1 do
          throwError "Unexpected number of fields for catch-all branch: {s.fields}"
        let sparseCasesOnEqName ← getSparseCasesOnEq matchDeclName
        let some (_, lhs) ← matchEqHEqLHS? (← s.mvarId.getType) | throwError "Target not an equality"
        let eqProof := mkConst sparseCasesOnEqName lhs.getAppFn.constLevels!
        let eqProof := mkAppN eqProof lhs.getAppArgs[:sparseCasesOnInfo.arity]
        let eqProof := mkApp eqProof s.fields[0]!
        rewriteGoalUsingEq s.mvarId eqProof
      else
        s.mvarId.modifyTargetEqLHS fun lhs =>
          unfoldDefinition lhs
  catch e =>
    trace[Meta.Match.matchEqs] "splitSparseCasesOn failed{indentD e.toMessageData}"
    throw e
