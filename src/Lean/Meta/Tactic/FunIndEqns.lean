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

def getFunCasesEqnName (fnName : Name) (i : Nat) : Name :=
  (fnName ++ `fun_cases_eq).appendIndexAfter (i + 1)

/-
When encountering a matcher, we want to rewrite its targets with the given hyps and see if we can iota-reduce,
but not reduce anything else.

This is a heuristic approximation.
-/
partial def simpWithNotUnderLambda (hyps : Array Expr) (e : Expr) : MetaM (Option Simp.Result) := do
    let mut ctxt ← Simp.mkContext
        (simpTheorems  := #[])
        (congrTheorems := (← getSimpCongrTheorems))
        (config        := { Simp.neutralConfig with beta := true, iota := true, proj := true })
    for h in hyps do
      if (← inferType h).isEq then
        let simpTheorems ← ctxt.simpTheorems.addTheorem (.fvar h.fvarId!) h (config := ctxt.indexConfig)
        ctxt := ctxt.setSimpTheorems simpTheorems
    let methods := {
      pre := Simp.rewritePre
      post := Simp.rewritePost
    }
    let rec go e : MetaM (Option Simp.Result) := do
      trace[Meta.FunInd] "simpWithNotUnderLambda step:{indentExpr e}"
      let (step, _) ← Simp.simpMatch e (Simp.Methods.toMethodsRef methods) ctxt |>.run {}
      match step with
      | .continue r =>
        return r
      | .visit r =>
        if let some r' ← go r.expr then
          some <$> r.mkEqTrans r'
        else
          return some r
      | .done r =>
        return r
    go e
 where
  noLambda : Simp.Simproc := fun e => do -- TODO: use this
    return if e.isLambda then .done { expr := e } else .continue

-- Iota reduction and reducing if-then-else
partial def simpEqnType (hyps : Array Expr) (e prf : Expr) : MetaM (Expr × Expr) := withReducible do
  unless e.isEq do throwError s!"not an equation: {e}"
  let rhs := e.appArg!
  let (rhs', prf') ← go hyps rhs prf
  trace[Meta.FunInd] "simpEqnType done:{indentExpr rhs}"
  let e' := e.appFn!.app rhs'
  return (← mkForallFVars hyps e', ← mkLambdaFVars hyps prf')
where
  go hyps e prf : MetaM (Expr × Expr) := do
    trace[Meta.FunInd] "simpEqnType step:{indentExpr e}"
    -- Reduce if-then-else
    match_expr e with
    | ite@ite α c hdec «then» «else» =>
      if let some h ← hyps.findM? (fun h => do isDefEq (← inferType h) c) then
        let prf' ← mkEqTrans prf (mkApp6 (.const ``if_pos ite.constLevels!) c hdec h α «then» «else»)
        return ← go hyps «then» prf'
      if let some h ← hyps.findM? (fun h => do isDefEq (← inferType h) (mkNot c)) then
        let prf' ← mkEqTrans prf (mkApp6 (.const ``if_neg ite.constLevels!) c hdec h α «then» «else»)
        return ← go hyps «else» prf'
      return (e, prf)
    | ite@dite α c hdec «then» «else» =>
      if let some h ← hyps.findM? (fun h => do isDefEq (← inferType h) c) then
        let prf' ← mkEqTrans prf (mkApp6 (.const ``dif_pos ite.constLevels!) c hdec h α «then» «else»)
        return ← go hyps («then».beta #[h]) prf'
      if let some h ← hyps.findM? (fun h => do isDefEq (← inferType h) (mkNot c)) then
        let prf' ← mkEqTrans prf (mkApp6 (.const ``dif_neg ite.constLevels!) c hdec h α «then» «else»)
        return ← go hyps («else».beta #[h]) prf'
      return (e, prf)
    | _ => pure ()

    -- Reduce let
    if e.isLet then
      for h in hyps do
        if (← withReducible (isDefEq h e.letValue!)) then
          return ← go hyps (e.letBody!.instantiate1 h) prf
      return (e, prf)

    -- Rewrite match targets and reduce
    if (← isMatcherApp e) then
      let r? ← simpWithNotUnderLambda hyps e
      if let some r := r? then
        let e' := r.expr
        if e' != e then
          let prf' ← mkEqTrans prf (← r.getProof)
          return ← go hyps e' prf'

    return (e, prf)


/-

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
    let simprocs := simprocs.addCore #[.star] `deduplicateLet false (.inl (deduplicateLet xs))
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
    r.addForalls xs
 where
  -- For the benefit of `if_pos` etc.
  discharge? (xs : Array Expr) : Simp.Discharge := fun prop => do
    for x in xs do
      if (← isDefEq prop (← inferType x)) then
        return some x
    return none
  deduplicateLet (xs : Array Expr) : Simp.Simproc := fun e => do
    logInfo m!"deduplicateLet {e}"
    if e.isLet then
      for x in xs do
        if (← withReducible (isDefEq x e.letValue!)) then
          return .visit { expr := e.bindingBody!.instantiate1 x }
    return .continue
  -/

def mkEqnVals (fnName : Name) : MetaM Unit := do
  withTraceNode `Meta.FunInd (pure m!"{exceptEmoji ·} mkEqnTypes {fnName}") do

  let fnVal ← getConstVal fnName
  let fnUs := fnVal.levelParams.map mkLevelParam
  let some unfoldEqName ← getUnfoldEqnFor? (nonRec := True) fnName
    | throwError "no unfolding theorem theorem for '{.ofConstName fnName}'"
  let some funIndInfo ← getFunIndInfo? (cases := true) fnName
    | throwError "no functional cases theorem for '{.ofConstName fnName}'"
  forallBoundedTelescope (cleanupAnnotations := true) fnVal.type funIndInfo.params.size fun xs _ => do

    -- Figure out params and targets
    let mut params := #[]
    let mut targets := #[]
    let mut us := #[]
    for u in fnUs, b in funIndInfo.levelMask do
      if b then
        us := us.push u
    for x in xs, kind in funIndInfo.params do
      match kind with
      | .dropped => pure ()
      | .param => params := params.push x
      | .target => targets := targets.push x
    trace[Meta.FunInd] "us: {us}\nparams: {params}\ntargets: {targets}"

    withLocalDeclD `motive (← mkForallFVars xs (.sort 0)) fun motive => do
      let motiveArg ← mkLambdaFVars targets (mkAppN motive xs)
      let elimExpr := mkAppN (.const funIndInfo.funIndName us.toList) (params.push motiveArg)
      let elimType ← inferType elimExpr
      let altTypes ← arrowDomainsN funIndInfo.numAlts elimType
      let _ ← altTypes.mapIdxM fun i altType => do
        forallLetTelescope altType fun altParams altBodyType => do
          unless altBodyType.getAppFn.isFVarOf motive.fvarId! do
            panic! s!"expected {altBodyType} to be an application of {motive}"
          assert! altBodyType.getAppNumArgs == xs.size

          let eqnExpr := mkAppN (.const unfoldEqName fnUs) altBodyType.getAppArgs
          let eqnType ← inferType eqnExpr
          let (eqnType', eqnExpr') ← simpEqnType altParams eqnType eqnExpr

          trace[Meta.FunInd] "Equation {i+1} before simp:{indentExpr eqnType}\nafter simp:{indentExpr eqnType'}"
          let eqnExpr' ← mkExpectedTypeHint eqnExpr' eqnType'
          let eqnExpr' ← mkLambdaFVars (usedOnly := true) xs eqnExpr'

          addDecl <| Declaration.thmDecl {
            name := getFunCasesEqnName fnName i,
            type := (← inferType eqnExpr'),
            value := eqnExpr'
            levelParams := fnVal.levelParams
          }

def realizeEqns (fnName : Name) : MetaM Unit := do
  -- let _ ← getFunInduct? (cases := true) fnName
  -- assert! (← getEnv).contains (getFunCasesName fnName)
  -- let info ← getConstInfo (getFunCasesName fnName)
  -- logInfo m!"fun_cases type: {info.type}"
  realizeConst fnName (getFunCasesEqnName fnName 0) do
    mkEqnVals fnName

def getEqnsFor (fnName : Name) : MetaM (Array Name) := do
  realizeEqns fnName
  -- let some funIndInfo ← getFunIndInfo? (cases := true) fnName
    -- | throwError "no functional cases theorem for '{.ofConstName fnName}'"
  let numAlts := 3 -- TODO
  return Array.ofFn (n := numAlts) fun i => getFunCasesEqnName fnName i

/-

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

/-
end Lean.Tactic.FunInd

def filter (p : α → Bool) (xs : List α) : List α :=
  match xs with
  | [] => []
  | x::xs =>
    if p x then
      x :: filter p xs
    else
      filter p xs


-- set_option trace.Meta.FunInd true
-- set_option trace.Meta.Tactic.simp true
-- set_option trace.Debug.Meta.Tactic.simp true

run_meta Lean.Tactic.FunInd.getEqnsFor ``filter
-- run_meta  mkEqnVals ``filter

#check filter.fun_cases_eq_1
#check filter.fun_cases_eq_2
#check filter.fun_cases_eq_3

-/
