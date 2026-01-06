/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.Simp.Result
import Lean.Meta.Sym.Simp.Simproc
import Lean.Meta.Sym.Simp.Congr
import Lean.Meta.Sym.Simp.Funext
namespace Lean.Meta.Sym.Simp
open Internal

def simpLambda (e : Expr) : SimpM Result := do
  -- **TODO**: Add free variable reuse
  lambdaTelescope e fun xs b => do
    match (← simp b) with
    | .rfl _ => return .rfl
    | .step b' h _ =>
      let h ← mkLambdaFVars xs h
      -- **TODO**: Add `mkLambdaFVarsS`?
      let e' ← shareCommonInc (← mkLambdaFVars xs b')
      let funext ← getFunext xs b
      return .step e' (mkApp3 funext e e' h)
where
  getFunext (xs : Array Expr) (b : Expr) : SimpM Expr := do
    let key ← inferType e
    if let some h := (← get).funext.find? { expr := key } then
      return h
    else
      let β ← inferType b
      let h ← mkFunextFor xs β
      modify fun s => { s with funext := s.funext.insert { expr := key } h }
      return h

def simpForall (_ : Expr) : SimpM Result := do
  -- **TODO**
  return .rfl

def simpLet (_ : Expr) : SimpM Result := do
  -- **TODO**
  return .rfl

def simpApp (e : Expr) : SimpM Result := do
  congrArgs e

def simpStep : Simproc := fun e => do
  match e with
  | .lit _ | .sort _ | .bvar _ | .const .. | .fvar _  | .mvar _ => return .rfl
  | .proj .. =>
    throwError "unexpected kernel projection term during simplification{indentExpr e}\npre-process and fold them as projection applications"
  | .mdata m b =>
    let r ← simp b
    match r with
    | .rfl _ => return .rfl
    | .step b' h _ => return .step (← mkMDataS m b') h
  | .lam .. => simpLambda e
  | .forallE .. => simpForall e
  | .letE .. => simpLet e
  | .app .. => simpApp e

abbrev cacheResult (e : Expr) (r : Result) : SimpM Result := do
  modify fun s => { s with cache := s.cache.insert { expr := e } r }
  return r

@[export lean_sym_simp]
def simpImpl (e₁ : Expr) : SimpM Result := withIncRecDepth do
  let numSteps := (← get).numSteps
  if numSteps >= (← getConfig).maxSteps then
    throwError "`simp` failed: maximum number of steps exceeded"
  if let some result := (← getCache).find? { expr := e₁ } then
    return result
  let numSteps := numSteps + 1
  if numSteps % 1000 == 0 then
    checkSystem "simp"
  modify fun s => { s with numSteps }
  let r₁ ← pre e₁
  match r₁ with
  | .rfl true | .step _ _ true => cacheResult e₁ r₁
  | .step e₂ h₁ false => cacheResult e₁ (← mkEqTransResult e₁ e₂ h₁ (← simp e₂))
  | .rfl false =>
  let r₂ ← (simpStep >> post) e₁
  match r₂ with
  | .rfl _ | .step _ _ true => cacheResult e₁ r₂
  | .step e₂ h₁ false => cacheResult e₁ (← mkEqTransResult e₁ e₂ h₁ (← simp e₂))

end Lean.Meta.Sym.Simp
