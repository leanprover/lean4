/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Basic
import Lean.Meta.Tactic.Contradiction

namespace Lean.Meta.Match

/--
A custom, approximated, and quick `contradiction` tactic.
It only finds contradictions of the form `(h₁ : p)` and `(h₂ : ¬ p)` where
`p`s are structurally equal. The procedure is not quadratic like `contradiction`.

We use it to improve the performance of `proveSubgoalLoop` at `mkSplitterProof`.
We will eventually have to write more efficient proof automation for this module.
The new proof automation should exploit the structure of the generated goals and avoid general purpose tactics
such as `contradiction`.
-/
private def _root_.Lean.MVarId.contradictionQuick (mvarId : MVarId) : MetaM Bool := do
  mvarId.withContext do
    let mut posMap : Std.HashMap Expr FVarId := {}
    let mut negMap : Std.HashMap Expr FVarId := {}
    for localDecl in (← getLCtx) do
      unless localDecl.isImplementationDetail do
        if let some p ← matchNot? localDecl.type then
          if let some pFVarId := posMap[p]? then
            mvarId.assign (← mkAbsurd (← mvarId.getType) (mkFVar pFVarId) localDecl.toExpr)
            return true
          negMap := negMap.insert p localDecl.fvarId
        if (← isProp localDecl.type) then
          if let some nFVarId := negMap[localDecl.type]? then
            mvarId.assign (← mkAbsurd (← mvarId.getType) localDecl.toExpr (mkFVar nFVarId))
            return true
          posMap := posMap.insert localDecl.type localDecl.fvarId
      pure ()
    return false

inductive InjectionAnyResult where
  | solved
  | failed
  /-- `fvarId` refers to the local declaration selected for the application of the `injection` tactic. -/
  | subgoal (fvarId : FVarId) (mvarId : MVarId)

def injectionAnyCandidate? (type : Expr) : MetaM (Option (Expr × Expr)) := do
  if let some (_, lhs, rhs) ← matchEq? type then
    return some (lhs, rhs)
  else if let some (α, lhs, β, rhs) ← matchHEq? type then
    if (← isDefEq α β) then
      return some (lhs, rhs)
  return none

/--
Try applying `injection` to a local declaration that is not in `forbidden`.

We use `forbidden` because the `injection` tactic might fail to clear the variable if there are forward dependencies.
See `proveSubgoalLoop` for additional details.
-/
def injectionAny (mvarId : MVarId) (forbidden : FVarIdSet := {}) : MetaM InjectionAnyResult := do
  mvarId.withContext do
    for localDecl in (← getLCtx) do
      unless forbidden.contains localDecl.fvarId do
        if let some (lhs, rhs) ← injectionAnyCandidate? localDecl.type then
          unless (← isDefEq lhs rhs) do
            let lhs ← whnf lhs
            let rhs ← whnf rhs
            unless lhs.isRawNatLit && rhs.isRawNatLit do
              try
                match (← injection mvarId localDecl.fvarId) with
                | InjectionResult.solved  => return InjectionAnyResult.solved
                | InjectionResult.subgoal mvarId .. => return InjectionAnyResult.subgoal localDecl.fvarId mvarId
              catch ex =>
                trace[Meta.Match.matchEqs] "injectionAnyFailed at {localDecl.userName}, error\n{ex.toMessageData}"
                pure ()
    return InjectionAnyResult.failed


/--
Solves the overlap assumptions expected by the alternative of a splitter
-/
public partial def solveOverlap (mvarId : MVarId) : MetaM Unit := do
    trace[Meta.Match.matchEqs] "solveOverlap {mkMVar mvarId}, {repr (← mvarId.getDecl).kind}\n{indentD mvarId}"
    let (_, mvarId) ← mvarId.intros
    loop mvarId {}
where
  /-
  `forbidden` tracks variables that we have already applied `injection`.
  Recall that the `injection` tactic may not be able to eliminate them when
  they have forward dependencies.
  -/
  loop (mvarId : MVarId) (forbidden : FVarIdSet) : MetaM Unit := do
    trace[Meta.Match.matchEqs] "proveSubgoalLoop\n{mvarId}"
    if (← mvarId.contradictionQuick) then
      return ()
    match (← injectionAny mvarId forbidden) with
    | .solved => return ()
    | .failed =>
      let mvarId' ← substVars mvarId
      if mvarId' == mvarId then
        if (← mvarId.contradictionCore {}) then
          return ()
        throwError "failed to solve overlap assumption, unsolved subgoal{indentD mvarId}"
      else
        loop mvarId' forbidden
    | .subgoal fvarId mvarId => loop mvarId (forbidden.insert fvarId)
