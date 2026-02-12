/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/

module

prelude
public import Lean.Meta.Sym.Simp.SimpM
public import Lean.Meta.Tactic.Cbv.Opaque
public import Lean.Meta.Tactic.Cbv.ControlFlow
import Lean.Meta.Tactic.Cbv.Util
import Lean.Meta.Tactic.Cbv.TheoremsLookup
import Lean.Meta.Tactic.Cbv.CbvEvalExt
import Lean.Meta.Sym
import Lean.Meta.Tactic.Refl

namespace Lean.Meta.Tactic.Cbv
open Lean.Meta.Sym.Simp

public register_builtin_option cbv.warning : Bool := {
  defValue := true
  descr    := "disable `cbv` usage warning"
}

def tryMatchEquations (appFn : Name) : Simproc := fun e => do
  let thms ← getMatchTheorems appFn
  thms.rewrite (d := dischargeNone) e

def tryEquations : Simproc := fun e => do
  unless e.isApp do
    return .rfl
  let some appFn := e.getAppFn.constName? | return .rfl
  let thms ← getEqnTheorems appFn
  thms.rewrite (d := dischargeNone) e

def tryUnfold : Simproc := fun e => do
  unless e.isApp do
    return .rfl
  let some appFn := e.getAppFn.constName? | return .rfl
  let some thm ← getUnfoldTheorem appFn | return .rfl
  Theorem.rewrite thm e

def tryMatcher : Simproc := fun e => do
  unless e.isApp do
    return .rfl
  let some appFn := e.getAppFn.constName? | return .rfl
  let some info ← getMatcherInfo? appFn | return .rfl
  let start := info.numParams + 1
  let stop  := start + info.numDiscrs
  (simpAppArgRange · start stop)
    >> tryMatchEquations appFn
      <|> reduceRecMatcher
        <| e

def handleConstApp : Simproc := fun e => do
  if (← isCbvOpaque e.getAppFn.constName!) then
    return .rfl (done := true)
  else
    tryEquations <|> tryUnfold <| e

def betaReduce : Simproc := fun e => do
  -- TODO: Improve term sharing
  let new := e.headBeta
  let new ← Sym.share new
  return .step new (← Sym.mkEqRefl new)

def tryCbvTheorems : Simproc := fun e => do
  let some fnName := e.getAppFn.constName? | return .rfl
  let some evalLemmas ← getCbvEvalLemmas fnName | return .rfl
  Theorems.rewrite evalLemmas (d := dischargeNone) e

def handleApp : Simproc := fun e => do
  unless e.isApp do return .rfl
  let fn := e.getAppFn
  match fn with
  | .const constName _ =>
    let info ← getConstInfo constName
    tryCbvTheorems <|> (guardSimproc (fun _ => info.hasValue) handleConstApp) <|> reduceRecMatcher <| e
  | .lam .. => betaReduce e
  | _ => return .rfl

def isOpaqueConst : Simproc := fun e => do
  let .const constName _ := e | return .rfl
  let hasTheorems := (← getCbvEvalLemmas constName).isSome
  if hasTheorems then
   let res ← (tryCbvTheorems) e
    match res with
    | .rfl false =>
      return .rfl
    | _ => return res
  else
    return .rfl (← isCbvOpaque constName)

def foldLit : Simproc := fun e => do
 let some n := e.rawNatLit? | return .rfl
 -- TODO: check performance of sharing
  return .step (← Sym.share <| mkNatLit n) (← Sym.mkEqRefl e)

def zetaReduce : Simproc := fun e => do
  let .letE _ _ value body _ := e | return .rfl
  let new := expandLet body #[value]
  -- TODO: Improve sharing
  let new ← Sym.share new
  return .step new (← Sym.mkEqRefl new)

def handleProj : Simproc := fun e => do
  let Expr.proj typeName idx struct := e | return .rfl
  -- We recursively simplify the projection
  let res ← simp struct
  match res with
  | .rfl _ =>
    let some reduced ← reduceProj? <| .proj typeName idx struct | do
      return .rfl (done := true)

    -- TODO: Figure if we can share this term incrementally
    let reduced ← Sym.share reduced
    return .step reduced (← Sym.mkEqRefl reduced)
  | .step e' proof _ =>
    let type ← Sym.inferType e'
    let congrArgFun := Lean.mkLambda `x .default type <| .proj typeName idx <| .bvar 0

    -- TODO: Create an efficient symbolic version of `mkCongrArg`
    let newProof ← mkCongrArg congrArgFun proof
    return .step (← Lean.Expr.updateProjS! e e') newProof

def simplifyAppFn : Simproc := fun e => do
    unless e.isApp do return .rfl
    let fn := e.getAppFn
    if fn.isLambda || fn.isConst then
      return .rfl
    else
    let res ← simp fn
    match (← simp fn) with
    | .rfl _ => return res
    | .step e' proof _ =>
      let newType ← Sym.inferType e'
      let congrArgFun := Lean.mkLambda `x .default newType (mkAppN (.bvar 0) e.getAppArgs)
      let newValue ← mkAppNS e' e.getAppArgs
      let newProof ← mkCongrArg congrArgFun proof
      return .step newValue newProof

def handleConst : Simproc := fun e => do
  trace[Meta.Tactic] "Trying const: {e}"
  let .const n _ := e | return .rfl
  let info ← getConstInfo n
  unless info.isDefinition do return .rfl
  let eType ← Sym.inferType e
  let eType ← whnfD eType
  if eType matches .forallE .. then return .rfl
  let some thm ← getUnfoldTheorem n |
    unless info.isCtor || info.isCtor do throwError "Cannot unfold {e}"
    return .rfl
  Theorem.rewrite thm e

def cbvPreStep : Simproc := fun e => do
  match e with
  | .lit .. => foldLit e
  | .proj .. => handleProj e
  | .const .. => isOpaqueConst >> handleConst <| e
  | .app .. => simpControlCbv <|> simplifyAppFn <| e
  | .letE .. =>
    if e.letNondep! then
      let betaAppResult ← toBetaApp e
      return .step (betaAppResult.e) (betaAppResult.h)
    else
      zetaReduce e
  | .forallE .. | .lam .. | .fvar .. | .mvar .. | .bvar .. | .sort .. => return .rfl (done := true)
  | _ => return .rfl

def cbvPre : Simproc := isBuiltinValue <|> isProofTerm <|> cbvPreStep

def cbvPost : Simproc := evalGround <|> handleApp

public def cbvEntry (e : Expr) : MetaM Result := do
  trace[Meta.Tactic.cbv] "Called cbv tactic to simplify {e}"
  let methods := {pre := cbvPre, post := cbvPost}
  let e ← Sym.unfoldReducible e
  Sym.SymM.run do
    let e ← Sym.shareCommon e
    SimpM.run' (simp e) (methods := methods)

public def cbvGoalCore (m : MVarId) (inv : Bool := false) : MetaM (Option MVarId) := do
  Sym.SymM.run do
    let methods := {pre := cbvPre, post := cbvPost}
    let m ← Sym.preprocessMVar m
    let mType ← m.getType
    let some (_, lhs, rhs) := mType.eq? | return m
    let (toReduce, toCompare) := if inv then (rhs, lhs) else (lhs, rhs)
    let result ← SimpM.run' (simp toReduce) (methods := methods)
    match result with
    | .rfl _ =>
      unless (← isDefEq toReduce toCompare) do return m
      m.refl
      return .none
    | .step e' proof _ =>
      if (← isDefEq e' toCompare) then
        if inv then
          m.assign (← mkEqSymm proof)
        else
          m.assign proof
        return .none
      else
        if inv then
          let newGoalType ← mkEq toCompare e'
          let newGoal ← mkFreshExprMVar newGoalType
          let toAssign ← mkEqTrans newGoal proof
          m.assign toAssign
          return newGoal.mvarId!
        else
          let newGoalType ← mkEq e' toCompare
          let newGoal ← mkFreshExprMVar newGoalType
          let toAssign ← mkEqTrans proof newGoal
          m.assign toAssign
          return newGoal.mvarId!

public def cbvGoal (m : MVarId) : MetaM (Option MVarId) := do
  match (← cbvGoalCore m (inv := false)) with
  | .none => return .none
  | .some m' => cbvGoalCore m' (inv := true)


end Lean.Meta.Tactic.Cbv
