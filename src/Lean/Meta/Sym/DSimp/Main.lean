/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.DSimp.DSimpM
import Lean.Meta.Sym.DSimp.DSimproc
import Lean.Meta.Sym.DSimp.App
import Lean.Meta.Sym.DSimp.Lambda
import Lean.Meta.Sym.DSimp.Forall
import Lean.Meta.Sym.DSimp.Let
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.InstantiateMVarsS
namespace Lean.Meta.Sym.DSimp
open Lean.Meta.Sym.Internal

def dsimpStep : DSimproc := fun e => do
  match e with
  | .lit _ | .sort _ | .bvar _ | .const .. | .fvar _ => return .rfl
  | .mvar _ =>
    let some e' ← instantiateAssignedMVarHeadS? e | return .rfl
    return .step e'
  | .proj .. =>
    throwError "unexpected kernel projection term during simplification{indentExpr e}\npre-process and fold them as projection applications"
  | .mdata _ b =>
    match (← dsimp b) with
    | .rfl _    => return .rfl
    | .step b' _ => return .step (← e.updateMDataS! b')
  | .lam ..     => dsimpLambda e
  | .forallE .. => dsimpForall e
  | .letE ..    => dsimpLet e
  | .app ..     => dsimpAppArgs e

abbrev cacheResult (e : Expr) (r : Result) : DSimpM Result := do
  if e.hasMVar then
    modify fun s => { s with transientCache := s.transientCache.insert { expr := e } r }
  else
    modify fun s => { s with cache := s.cache.insert { expr := e } r }
  return r

set_option compiler.ignoreBorrowAnnotation true in
@[export lean_sym_dsimp]
def dsimpImpl (e₁ : Expr) : DSimpM Result := withIncRecDepth do
  let numSteps := (← get).numSteps
  if numSteps >= (← getConfig).maxSteps then
    throwError "`dsimp` failed: maximum number of steps exceeded"
  let key : ExprPtr := { expr := e₁ }
  let s ← get
  if let some r := (if e₁.hasMVar then s.transientCache else s.cache).find? key then
    return r
  let numSteps := numSteps + 1
  if numSteps % 1000 == 0 then
    checkSystem "dsimp"
  modify fun s => { s with numSteps }
  let r ← pre e₁
  let r ← match r with
    | .rfl true | .step _ true  => pure r
    | .step e₂ false  =>
      match (← dsimp e₂) with
      | .rfl done     => pure (.step e₂ done)
      | .step e₃ done => pure (.step e₃ done)
    | .rfl false =>
      let r ← (dsimpStep >> post) e₁
      match r with
      | .rfl _ | .step _ true => pure r
      | .step e₂ false =>
        match (← dsimp e₂) with
        | .rfl done     => pure (.step e₂ done)
        | .step e₃ done => pure (.step e₃ done)
  cacheResult e₁ r

end Lean.Meta.Sym.DSimp
