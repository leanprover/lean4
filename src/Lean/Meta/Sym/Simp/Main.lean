/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Tactic.Grind.AlphaShareBuilder
import Lean.Meta.Sym.Simp.Result
import Lean.Meta.Sym.Simp.Simproc
import Lean.Meta.Sym.Simp.Congr
namespace Lean.Meta.Sym.Simp
open Grind

def simpLambda (_ : Expr) : SimpM Result := do
  -- **TODO**
  return .rfl

def simpForall (_ : Expr) : SimpM Result := do
  -- **TODO**
  return .rfl

def simpLet (_ : Expr) : SimpM Result := do
  -- **TODO**
  return .rfl

def simpFVar (_ : Expr) : SimpM Result := do
  -- **TODO**
  return .rfl

def simpMVar (_ : Expr) : SimpM Result := do
  -- **TODO**
  return .rfl

def simpApp (e : Expr) : SimpM Result := do
  congrArgs e

def simpStep : Simproc := fun e => do
  match e with
  | .lit _ | .sort _ | .bvar _ | .const .. => return .rfl
  | .proj .. =>
    reportIssue! "unexpected kernel projection term during simplification{indentExpr e}\npre-process and fold them as projection applications"
    return .rfl
  | .mdata m b =>
    let r ← simp b
    match r with
    | .rfl => return .rfl
    | .step b' h => return .step (← mkMDataS m b') h
  | .lam .. => simpLambda e
  | .forallE .. => simpForall e
  | .letE .. => simpLet e
  | .fvar .. => simpFVar e
  | .mvar .. => simpMVar e
  | .app .. => simpApp e

abbrev cacheResult (e : Expr) (r : Result) : SimpM Result := do
  modify fun s => { s with cache := s.cache.insert { expr := e } r }
  return r

@[export lean_sym_simp]
def simpImpl (e₁ : Expr) : SimpM Result := do
  if (← get).numSteps >= (← getConfig).maxSteps then
    throwError "`simp` failed: maximum number of steps exceeded"
  if let some result := (← getCache).find? { expr := e₁ } then
    return result
  -- match (← pre e₁) with
  -- | .step e₂ h₁ => cacheResult e₁ (← mkEqTransResult e₁ e₂ h₁ (← simp e₂))
  -- | .rfl =>
  let r₁ ← (simpStep >> post) e₁
  match r₁ with
  | .rfl => cacheResult e₁ r₁
  | .step e₂ h₁ => cacheResult e₁ (← mkEqTransResult e₁ e₂ h₁ (← simp e₂))

end Lean.Meta.Sym.Simp
