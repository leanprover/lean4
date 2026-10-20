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

open Lean.Meta.Sym.Internal

/--
Returns `true` if `e` is a numeral application whose arguments are not visited:
`OfNat.ofNat _ n _`, `Char.ofNat n`, and `OfScientific.ofScientific _ _ m _ e` with raw
literals `n`, `m`, `e`. Like `Meta.simp`, `simp` treats these as atoms; see `simpStep`.
-/
def isLitApp (e : Expr) : Bool :=
  (e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 1).isRawNatLit) ||
  e.isCharLit ||
  (e.isAppOfArity ``OfScientific.ofScientific 5 && (e.getArg! 2).isRawNatLit && (e.getArg! 4).isRawNatLit)

/--
The structural step of `simp`: visits the subterms of `e` and rebuilds `e` from their
normal forms.

**Note**:
Like `Meta.simp`, an orphan raw `Nat` literal `n` is folded into
`OfNat.ofNat Nat n _`, the canonical numeral form that the literal recognizers
(`getNatValue?`, `evalGround`, the arithmetic normalizer) expect; rewrite rules
whose pattern variable binds the raw literal of a numeral produce such orphans, e.g.
`(OfNat.ofNat a : Fin n).val = a % n` applied to `(0 : Fin n).val`. Numeral applications
are not visited, so the raw literal inside them stays raw.
-/
def simpStep : Simproc := fun e => do
  match e with
  | .lit (.natVal n) =>
    let e' ← share (mkNatLit n)
    return .step e' (← mkEqRefl e')
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
  | .app .. => if isLitApp e then return .rfl else simpAppArgs e

set_option compiler.ignoreBorrowAnnotation true in
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
