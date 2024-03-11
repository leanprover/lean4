/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Rename
import Lean.Elab.SyntheticMVars
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.WF.TerminationArgument
import Lean.Meta.ArgsPacker

namespace Lean.Elab.WF
open Meta
open Term

def elabWFRel (preDefs : Array PreDefinition) (unaryPreDefName : Name) (prefixArgs : Array Expr)
    (argsPacker : ArgsPacker) (argType : Expr) (termArgs : TerminationArguments)
    (k : Expr → TermElabM α) : TermElabM α := do
  let α := argType
  let u ← getLevel α
  let expectedType := mkApp (mkConst ``WellFoundedRelation [u]) α
  trace[Elab.definition.wf] "elabWFRel start: {(← mkFreshTypeMVar).mvarId!}"
  withDeclName unaryPreDefName do
    let mainMVarId := (← mkFreshExprSyntheticOpaqueMVar expectedType).mvarId!
    let [fMVarId, wfRelMVarId, _] ← mainMVarId.apply (← mkConstWithFreshMVarLevels ``invImage) | throwError "failed to apply 'invImage'"
    let packedF ← argsPacker.uncurryND (termArgs.map (·.fn.beta prefixArgs))
    unless (←isDefEq (mkMVar fMVarId) packedF) do
      let msg := m!"invalid termination argument, expected{indentExpr (←inferType (mkMVar fMVarId))}\ngot{indentExpr (← inferType packedF)}"
      throwError msg
    -- fMVarId.assign packedF
    /-
    TODO: Type checking

    let (d, fMVarId) ← fMVarId.intro1
    let subgoals ← unpackMutual preDefs fMVarId d
    for (d, mvarId) in subgoals, termarg in termargs, preDef in preDefs do
      let mvarId ← unpackUnary preDef fixedPrefixSize mvarId d termarg
      mvarId.withContext do
        let errorMsgHeader? := if preDefs.size > 1 then
          "The termination argument types differ for the different functions, or depend on the " ++
          "function's varying parameters. Try using `sizeOf` explicitly:\nThe termination argument"
        else
          "The termination argument depends on the function's varying parameters. Try using " ++
          "`sizeOf` explicitly:\nThe termination argument"
        let value ← Term.withSynthesize <| elabTermEnsuringType element.body (← mvarId.getType)
            (errorMsgHeader? := errorMsgHeader?)
        mvarId.assign value
    -/
    let wfRelVal ← synthInstance (← inferType (mkMVar wfRelMVarId))
    wfRelMVarId.assign wfRelVal
    k (← instantiateMVars (mkMVar mainMVarId))

end Lean.Elab.WF
