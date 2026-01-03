/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Tactic.Grind.AlphaShareBuilder
import Lean.Meta.Sym.Simp.EqTrans
import Lean.Meta.Sym.Simp.Result
import Lean.Meta.Sym.Simp.Simproc
import Lean.Meta.Sym.Simp.Congr
namespace Lean.Meta.Sym.Simp
open Grind

def simpConst (e : Expr) : SimpM Result := do
  -- **TODO**
  return { expr := e }

def simpLambda (e : Expr) : SimpM Result := do
  -- **TODO**
  return { expr := e }

def simpForall (e : Expr) : SimpM Result := do
  -- **TODO**
  return { expr := e }

def simpLet (e : Expr) : SimpM Result := do
  -- **TODO**
  return { expr := e }

def simpFVar (e : Expr) : SimpM Result := do
  -- **TODO**
  return { expr := e }

def simpMVar (e : Expr) : SimpM Result := do
  -- **TODO**
  return { expr := e }

def simpApp (e : Expr) : SimpM Result := do
  congrArgs e

def simpStep : Simproc := fun e => do
  match e with
  | .lit _ | .sort _ | .bvar _ => return { expr := e }
  | .proj .. =>
    reportIssue! "unexpected kernel projection term during simplification{indentExpr e}\npre-process and fold them as projection applications"
    return { expr := e }
  | .mdata m b =>
    let r ← simp b
    if isSameExpr r.expr b then return { expr := e }
    else return { r with expr := (← mkMDataS m r.expr) }
  | .const .. => simpConst e
  | .lam .. => simpLambda e
  | .forallE .. => simpForall e
  | .letE .. => simpLet e
  | .fvar .. => simpFVar e
  | .mvar .. => simpMVar e
  | .app .. => simpApp e

def cacheResult (e : Expr) (r : Result) : SimpM Result := do
  modify fun s => { s with cache := s.cache.insert { expr := e } r }
  return r

@[export lean_sym_simp]
def simpImpl (e : Expr) : SimpM Result := do
  if (← get).numSteps >= (← getConfig).maxSteps then
    throwError "`simp` failed: maximum number of steps exceeded"
  if let some result := (← getCache).find? { expr := e } then
    return result
  let r ← (pre >> simpStep >> post) e
  if isSameExpr r.expr e then
    cacheResult e r
  else
    let r' ← simp r.expr
    if isSameExpr r'.expr r.expr then
      cacheResult e r
    else
      cacheResult e (← mkEqTrans e r r')

end Lean.Meta.Sym.Simp
