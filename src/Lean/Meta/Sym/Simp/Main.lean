/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.MonadSimp
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.InferType
import Lean.Meta.Sym.Simp.Result
import Lean.Meta.Sym.Simp.Simproc
import Lean.Meta.Sym.Simp.App
import Lean.Meta.Sym.Simp.Have
import Lean.Meta.Sym.Simp.Lambda
namespace Lean.Meta.Sym.Simp
open Internal

def simpArrow (e : Expr) : SimpM Result := do
  let p := e.bindingDomain!
  let q := e.bindingBody!
  match (← simp p), (← simp q) with
  | .rfl _, .rfl _ =>
    return .rfl
  | .step p' h _, .rfl _ =>
    let u ← getLevel p
    let v ← getLevel q
    let e' ← e.updateForallS! p' q
    return .step e' <| mkApp4 (mkConst ``implies_congr_left [u, v]) p p' q h
  | .rfl _, .step q' h _ =>
    let u ← getLevel p
    let v ← getLevel q
    let e' ← e.updateForallS! p q'
    return .step e' <| mkApp4 (mkConst ``implies_congr_right [u, v]) p q q' h
  | .step p' h₁ _, .step q' h₂ _ =>
    let u ← getLevel p
    let v ← getLevel q
    let e' ← e.updateForallS! p' q'
    return .step e' <| mkApp6 (mkConst ``implies_congr [u, v]) p p' q q' h₁ h₂

def simpForall (e : Expr) : SimpM Result := do
  if e.isArrow then
    simpArrow e
  else if (← isProp e) then
    let n := getForallTelescopeSize e.bindingBody! 1
    forallBoundedTelescope e n fun xs b => do
    match (← simp b) with
    | .rfl _ => return .rfl
    | .step b' h _ =>
      let h ← mkLambdaFVars xs h
      let e' ← shareCommonInc (← mkForallFVars xs b')
      -- **Note**: consider caching the forall-congr theorems
      let hcongr ← mkForallCongrFor xs
      return .step e' (mkApp3 hcongr (← mkLambdaFVars xs b) (← mkLambdaFVars xs b') h)
  else
    return .rfl
where
  -- **Note**: Optimize if this is quadratic in practice
  getForallTelescopeSize (e : Expr) (n : Nat) : Nat :=
    match e with
    | .forallE _ _ b _ => if b.hasLooseBVar 0 then getForallTelescopeSize b (n+1) else n
    | _ => n

def simpLet (e : Expr) : SimpM Result := do
  if !e.letNondep! then
    /-
    **Note**: We don't do anything if it is a dependent `let`.
    Users may decide to `zeta`-expand them or apply `letToHave` at `pre`/`post`.
    -/
    return .rfl
  else
    simpHaveAndZetaUnused e

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
  | .app .. => simpAppArgs e

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
