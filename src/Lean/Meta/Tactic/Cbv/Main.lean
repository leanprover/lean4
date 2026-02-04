/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/

module

prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Tactic.Cbv.Util
import Lean.Meta.Tactic.Cbv.TheoremsLookup
import Lean.Meta.Sym

namespace Lean.Meta.Tactic.Cbv
open Lean.Meta.Sym.Simp

public register_builtin_option cbv.warning : Bool := {
  defValue := true
  descr    := "disable `cbv` usage warning"
}

def skipBinders : Simproc := fun e => do
  return .rfl (e.isLambda || e.isForall)

def tryMatchEquations (appFn : Name) : Simproc := fun e => do
  let thms ← getMatchTheorems appFn
  thms.rewrite (d := dischargeNone) e

def reduceRecMatcher : Simproc := fun e => do
  if let some e' ← reduceRecMatcher? e then
    return .step e' (← Sym.mkEqRefl e')
  else
    return .rfl

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

def handleConstApp : Simproc :=
  tryEquations <|> tryUnfold

def betaReduce : Simproc := fun e => do
  -- TODO: Improve term sharing
  let new := e.headBeta
  let new ← Sym.share new
  return .step new (← Sym.mkEqRefl new)

def handleApp : Simproc := fun e => do
  unless e.isApp do return .rfl
  let fn := e.getAppFn
  match fn with
  | .const constName _ =>
    let info ← getConstInfo constName
    (guardSimproc (fun _ => info.hasValue) handleConstApp) <|> reduceRecMatcher <| e
  | .lam .. => betaReduce e
  | _ => return .rfl

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
    unless fn.isLambda || fn.isConst do
      let res ← simp fn
      match res with
      | .rfl _ => return res
      | .step e' proof _ =>
        let newType ← Sym.inferType e'
        let congrArgFun := Lean.mkLambda `x .default newType (mkAppN (.bvar 0) e.getAppArgs)
        let newValue ← mkAppNS e' e.getAppArgs
        let newProof ← mkCongrArg congrArgFun proof
        return .step newValue newProof
    return .rfl

def handleConst : Simproc := fun e => do
  let .const n _ := e | return .rfl
  let info ← getConstInfo n
  unless info.isDefinition do return .rfl
  let eType ← Sym.inferType e
  let eType ← whnfD eType
  unless eType matches .forallE .. do
    return .rfl
  -- TODO: Check if we need to look if we applied all the levels correctly
  let some thm ← getUnfoldTheorem n | return .rfl
  Theorem.rewrite thm e

def cbvPre : Simproc :=
      isBuiltinValue <|> isProofTerm <|> skipBinders
  >>  (tryMatcher >> simpControl) <|> (handleConst <|> simplifyAppFn <|> handleProj)

def cbvPost : Simproc :=
      evalGround
  >>  (handleApp <|> zetaReduce)
  >>  foldLit

public def cbvEntry (e : Expr) : MetaM Result := do
  trace[Meta.Tactic.cbv] "Called cbv tactic to simplify {e}"
  let methods := {pre := cbvPre, post := cbvPost}
  let e ← Sym.unfoldReducible e
  Sym.SymM.run do
    let e ← Sym.shareCommon e
    SimpM.run' (simp e) (methods := methods)

end Lean.Meta.Tactic.Cbv
