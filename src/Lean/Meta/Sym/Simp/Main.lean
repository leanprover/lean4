/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.Simp.Simproc
import Lean.Meta.Sym.Simp.App
import Lean.Meta.Sym.Simp.Have
import Lean.Meta.Sym.Simp.Forall

namespace Lean.Meta.Sym.Simp
builtin_initialize registerTraceClass `sym.simp.debug.cache

open Internal

def simpStep : Simproc := fun e => do
  match e with
  | .lit _ | .sort _ | .bvar _ | .const .. | .fvar _  | .mvar _ => return .rfl
  | .proj .. =>
    throwError "unexpected kernel projection term during simplification{indentExpr e}\npre-process and fold them as projection applications"
  | .mdata m b =>
    -- Propagate `cd` from inner term through the mdata wrapper.
    let r ← simp b
    match r with
    | .rfl _ cd => return mkRflResultCD cd
    | .step b' h _ cd => return .step (← mkMDataS m b') h (contextDependent := cd)
  | .lam .. => simpLambda e
  | .forallE .. => simpForall e
  | .letE .. => simpLet e
  | .app .. => simpAppArgs e

abbrev cacheResult (e : Expr) (r : Result) : SimpM Result := do
  if r.isContextDependent then
    modify fun s => { s with transientCache := s.transientCache.insert { expr := e } r }
  else
    modify fun s => { s with persistentCache := s.persistentCache.insert { expr := e } r }
  return r

@[export lean_sym_simp]
def simpImpl (e₁ : Expr) : SimpM Result := withIncRecDepth do
  let numSteps := (← get).numSteps
  if numSteps >= (← getConfig).maxSteps then
    throwError "`simp` failed: maximum number of steps exceeded"
  let key : ExprPtr := { expr := e₁ }
  if let some result := (← get).persistentCache.find? key then
    trace[sym.simp.debug.cache] "persistent cache hit: {e₁}"
    return result
  if let some result := (← get).transientCache.find? key then
    trace[sym.simp.debug.cache] "transient cache hit: {e₁}"
    return result
  let numSteps := numSteps + 1
  if numSteps % 1000 == 0 then
    checkSystem "simp"
  modify fun s => { s with numSteps }
  let r₁ ← pre e₁
  match r₁ with
  | .rfl true _ | .step _ _ true _ => cacheResult e₁ r₁
  | .step e₂ h₁ false cd₁ => cacheResult e₁ (← mkEqTransResult e₁ e₂ h₁ (← simp e₂) cd₁)
  | .rfl false cd₁ =>
  let r₂ ← (simpStep >> post) e₁
  -- If `pre` was context-dependent (cd₁ = true) but returned `.rfl`, it might
  -- succeed in another context. Propagate cd₁ so the cached result for `e₁`
  -- lands in the transient cache and gets re-evaluated after binder entry.
  let r₂ := if cd₁ && !r₂.isContextDependent then r₂.withContextDependent else r₂
  match r₂ with
  | .rfl _ _ | .step _ _ true _ => cacheResult e₁ r₂
  | .step e₂ h₁ false cd₁ => cacheResult e₁ (← mkEqTransResult e₁ e₂ h₁ (← simp e₂) cd₁)

end Lean.Meta.Sym.Simp
