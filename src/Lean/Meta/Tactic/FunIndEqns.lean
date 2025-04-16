/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

import Lean.Meta.Tactic.FunIndInfo
import Lean.Meta.Tactic.FunInd
import Lean.Elab.PreDefinition.Eqns
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Core

namespace Lean.Tactic.FunInd

open Lean Elab Meta

-- Iota reduction and reducing if-then-else
def simpEqnType (e : Expr) : MetaM Expr := withReducible do
  forallTelescope e fun xs e => do
    let mut s : SimpTheorems := {}
    s ← s.addConst ``if_pos (post := false)
    s ← s.addConst ``if_neg (post := false)
    s ← s.addConst ``dif_pos (post := false)
    s ← s.addConst ``dif_neg (post := false)
    let mut ctxt ← Simp.mkContext
        (simpTheorems  := #[s])
        (congrTheorems := (← getSimpCongrTheorems))
        (config        := { Simp.neutralConfig with iota := true })
    let simprocs : Simprocs := {}
    for h in xs do
      if (← inferType h).isEq then
        -- We add all equations provided by the induction principle.
        -- This can do more rewriting than excepted. We could instead write a
        -- simproc that looks for matchers where we can rewrite the discriminant
        -- using these equations, and that would iota-reduce afterwards, but
        -- not rewrite anywhere else.
        trace[Meta.FunInd] "Using assumption for rewriting: {h} : {← inferType h}"
        let simpTheorems ← ctxt.simpTheorems.addTheorem (.fvar h.fvarId!) h (config := ctxt.indexConfig)
        ctxt := ctxt.setSimpTheorems simpTheorems
    let (r, _stats) ← simp e ctxt (simprocs := #[simprocs])
      (discharge? := discharge? xs)
    mkForallFVars xs r.expr
 where
  -- For the benefit of `if_pos` etc.
  discharge? (xs : Array Expr) : Simp.Discharge := fun prop => do
    for x in xs do
      if (← isDefEq prop (← inferType x)) then
        return some x
    return none

def mkEqnTypes (fnName : Name) : MetaM (Array Expr) := do
  withTraceNode `Meta.FunInd (pure m!"{exceptEmoji ·} mkEqnTypes {fnName}") do
  let unfoldEq ← Eqns.unfoldThmType fnName
  forallTelescope (cleanupAnnotations := true) unfoldEq fun xs unfoldEq => do
    let some (_, lhs, _rhs) := unfoldEq.eq? |
      throwError "expected equation type, but got {unfoldEq}"
    lhs.withApp fun fn funArgs => do
      unless fn.isConstOf fnName do throwError "unexected LHS {lhs}"
      let fnUs := fn.constLevels!
      let some funIndInfo ← getFunIndInfo? (cases := true) fnName |
        throwError "no functional cases theorem for '{.ofConstName fnName}'"
      if funArgs.size != funIndInfo.params.size then
        throwError "Expected fully applied application of '{.ofConstName fnName}' with \
          {funIndInfo.params.size} arguments, but found {funArgs.size} arguments"
      let mut params := #[]
      let mut targets := #[]
      let mut us := #[]
      for u in fnUs, b in funIndInfo.levelMask do
        if b then
          us := us.push u
      for a in funArgs, kind in funIndInfo.params do
        match kind with
        | .dropped => pure ()
        | .param => params := params.push a
        | .target => targets := targets.push a
      trace[Meta.FunInd] "us: {us}\nparams: {params}\ntargets: {targets}"

      let elimExpr := mkAppN (.const funIndInfo.funIndName us.toList) params
      let elimInfo ← getElimExprInfo elimExpr
      unless targets.size = elimInfo.targetsPos.size do
        throwError "arity confusion trying to use \
          {.ofConstName funIndInfo.funIndName}. Does it take {targets.size} or \
          {elimInfo.targetsPos.size} targets?"

      let motive ← mkLambdaFVars targets unfoldEq
      let elimExpr := mkApp elimExpr motive

      let numAlts := elimInfo.altsInfo.size
      let eqnTypes ← inferArgumentTypesN numAlts elimExpr
      eqnTypes.mapIdxM fun i eqnType => do
        let eqnType' ← simpEqnType eqnType
        trace[Meta.FunInd] "Equation {i+1} before simp:{indentExpr eqnType}\nafter simp:{indentExpr eqnType'}"
        mkForallFVars (usedOnly := true) xs eqnType'

/-
def deriveFunIndEqns (fnName : Name) : MetaM Unit := do
  let funCaseName := getFunCasesName fnName
  let firstEqnName := funCaseName ++ `eq_1
  realizeConst funCaseName firstEqnName do
    _



def isFunIndEqnName (env : Environment) (name : Name) : Bool := Id.run do
  let .str p s := name | return false
  return "eq_".isPrefixOf s && (s.drop 3).isNat && isFunCasesName env p

builtin_initialize
  registerReservedNamePredicate isFunIndEqnName

  registerReservedNameAction fun name => do
    if isFunIndEqnName (← getEnv) name then
      let .str (.str p _) _ := name | return false
      MetaM.run' <| deriveFunIndEqns p
      return true
    return false

-/


def filter (p : α → Bool) (xs : List α) : List α :=
  match xs with
  | [] => []
  | x::xs =>
    if p x then
      x :: filter p xs
    else
      filter p xs


/-
set_option trace.Meta.FunInd true
set_option trace.Meta.Tactic.simp true
set_option trace.Debug.Meta.Tactic.simp true
-/

run_meta
  let eqns ← mkEqnTypes ``filter
  eqns.mapM (logInfo m!"{·}")
