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

/--
The termination arguments must not depend on the varying parameters of the function, and in
a mutual clique, they must be the same for all functions.

This ensures the preconditions for `ArgsPacker.uncurryND`.
-/
def checkCodomains (names : Array Name) (prefixArgs : Array Expr) (arities : Array Nat)
    (termArgs : TerminationArguments) : TermElabM Unit := do
  let mut codomains := #[]
  for name in names, arity in arities, termArg in termArgs do
    let type ← inferType (termArg.fn.beta prefixArgs)
    let codomain ← forallBoundedTelescope type arity fun xs codomain => do
      let fvars := xs.map (·.fvarId!)
      if codomain.hasAnyFVar (fvars.contains ·) then
        throwErrorAt termArg.ref  m!"The termination argument's type must not depend on the  " ++
          m!"function's varying parameters, but {name}'s termination argument does:{indentExpr type}\n" ++
          "Try using `sizeOf` explicitly"
      pure codomain
    codomains := codomains.push codomain

  let codomain0 := codomains[0]!
  for h : i in [1 : codomains.size] do
    unless ← isDefEqGuarded codomain0 codomains[i] do
      throwErrorAt termArgs[i]!.ref m!"The termination arguments of mutually recursive functions " ++
        m!"must have the same return type, but the termination argument of {names[0]!} has type" ++
        m!"{indentExpr codomain0}\n" ++
        m!"while the termination argument of {names[i]!} has type{indentExpr codomains[i]}\n" ++
        "Try using `sizeOf` explicitly"

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
    checkCodomains (preDefs.map (·.declName)) prefixArgs argsPacker.arities termArgs
    let termArgs := termArgs.map (·.fn.beta prefixArgs)
    let packedF ← argsPacker.uncurryND termArgs
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
