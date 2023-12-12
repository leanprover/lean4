/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Data.LBool
import Lean.Meta.InferType
import Lean.Meta.AppBuilder

namespace Lean.Meta

private abbrev withInstantiatedMVars (e : Expr) (k : Expr → OptionT MetaM α) : OptionT MetaM α := do
  let eNew ← instantiateMVars e
  if eNew.getAppFn.isMVar then
    failure
  else
    k eNew

def isNatProjInst (declName : Name) (numArgs : Nat) : Bool :=
      (numArgs == 4 && (declName == ``Add.add || declName == ``Sub.sub || declName == ``Mul.mul))
   || (numArgs == 6 && (declName == ``HAdd.hAdd || declName == ``HSub.hSub || declName == ``HMul.hMul))
   || (numArgs == 3 && declName == ``OfNat.ofNat)

/--
  Evaluate simple `Nat` expressions.
  Remark: this method assumes the given expression has type `Nat`. -/
partial def evalNat (e : Expr) : OptionT MetaM Nat := do
  match e with
  | .lit (.natVal n)     => return n
  | .mdata _ e           => evalNat e
  | .const ``Nat.zero .. => return 0
  | .app ..              => visit e
  | .mvar ..             => visit e
  | _                    => failure
where
  visit e := do
    let f := e.getAppFn
    match f with
    | .mvar .. => withInstantiatedMVars e evalNat
    | .const c _ =>
      let nargs := e.getAppNumArgs
      if c == ``Nat.succ && nargs == 1 then
        let v ← evalNat (e.getArg! 0)
        return v+1
      else if c == ``Nat.add && nargs == 2 then
        let v₁ ← evalNat (e.getArg! 0)
        let v₂ ← evalNat (e.getArg! 1)
        return v₁ + v₂
      else if c == ``Nat.sub && nargs == 2 then
        let v₁ ← evalNat (e.getArg! 0)
        let v₂ ← evalNat (e.getArg! 1)
        return v₁ - v₂
      else if c == ``Nat.mul && nargs == 2 then
        let v₁ ← evalNat (e.getArg! 0)
        let v₂ ← evalNat (e.getArg! 1)
        return v₁ * v₂
      else if isNatProjInst c nargs then
        evalNat (← unfoldProjInst? e)
      else
        failure
    | _ => failure

mutual

/--
Quick function for converting `e` into `s + k` s.t. `e` is definitionally equal to `Nat.add s k`.
This function always succeeds in finding such `s` and `k`
(as a last resort it returns `e` and `0`).
-/
private partial def getOffset (e : Expr) : MetaM (Expr × Nat) :=
  return (← isOffset? e).getD (e, 0)

/--
Similar to `getOffset` but returns `none` if the expression is not syntactically an offset.
-/
private partial def isOffset? (e : Expr) : OptionT MetaM (Expr × Nat) := do
  match e with
  | .app _ a => do
    let f := e.getAppFn
    match f with
    | .mvar .. => withInstantiatedMVars e isOffset?
    | .const c _ =>
      let nargs := e.getAppNumArgs
      if c == ``Nat.succ && nargs == 1 then
        let (s, k) ← getOffset a
        pure (s, k+1)
      else if c == ``Nat.add && nargs == 2 then
        let v ← evalNat (e.getArg! 1)
        let (s, k) ← getOffset (e.getArg! 0)
        pure (s, k+v)
      else if (c == ``Add.add && nargs == 4) || (c == ``HAdd.hAdd && nargs == 6) then
        isOffset? (← unfoldProjInst? e)
      else
        failure
    | _ => failure
  | _ => failure

end

private def isNatZero (e : Expr) : MetaM Bool := do
  match (← evalNat e) with
  | some v => return v == 0
  | _      => return false

private def mkOffset (e : Expr) (offset : Nat) : MetaM Expr := do
  if offset == 0 then
    return e
  else if (← isNatZero e) then
    return mkNatLit offset
  else
    mkAdd e (mkNatLit offset)

def isDefEqOffset (s t : Expr) : MetaM LBool := do
  let ifNatExpr (x : MetaM LBool) : MetaM LBool := do
    let type ← inferType s
    -- Remark: we use `withNewMCtxDepth` to make sure we don't assign metavariables when performing the `isDefEq` test
    if (← withNewMCtxDepth <| Meta.isExprDefEqAux type (mkConst ``Nat)) then
      x
    else
      return LBool.undef
  let isDefEq (s t) : MetaM LBool :=
    ifNatExpr <| toLBoolM <| Meta.isExprDefEqAux s t
  if !(← getConfig).offsetCnstrs then
    return LBool.undef
  else
    match (← isOffset? s) with
    | some (s, k₁) =>
      match (← isOffset? t) with
      | some (t, k₂) => -- s+k₁ =?= t+k₂
        if k₁ == k₂ then
          isDefEq s t
        else if k₁ < k₂ then
          isDefEq s (← mkOffset t (k₂ - k₁))
        else
          isDefEq (← mkOffset s (k₁ - k₂)) t
      | none =>
        match (← evalNat t) with
        | some v₂ => -- s+k₁ =?= v₂
          if v₂ ≥ k₁ then
            isDefEq s (mkNatLit <| v₂ - k₁)
          else
            ifNatExpr <| return LBool.false
        | none =>
          return LBool.undef
    | none =>
      match (← evalNat s) with
      | some v₁ =>
        match (← isOffset? t) with
        | some (t, k₂) => -- v₁ =?= t+k₂
          if v₁ ≥ k₂ then
            isDefEq (mkNatLit <| v₁ - k₂) t
          else
            ifNatExpr <| return LBool.false
        | none =>
          match (← evalNat t) with
          | some v₂ => ifNatExpr <| return (v₁ == v₂).toLBool -- v₁ =?= v₂
          | none    => return LBool.undef
      | none => return LBool.undef

end Lean.Meta
