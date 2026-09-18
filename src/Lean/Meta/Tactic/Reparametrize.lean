/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Lean.Meta.Basic
import Lean.Meta.WHNF
import Lean.Structure
import Lean.ProjFns

public section

namespace Lean.Meta.OneFieldStructure

/--
A one-field-structure constructor or projection, together with
a choice of parameters and universe levels for the underlying structure.
-/
structure Bijection where
  isCtor : Bool
  ctorVal : ConstructorVal
  us : List Level
  params : Array Expr

def Bijection.inv (b : Bijection) : Bijection :=
  { b with isCtor := !b.isCtor }

protected def Bijection.mkApp (b : Bijection) (e : Expr) : MetaM Expr :=
  if b.isCtor then
    return mkApp (mkAppN (mkConst b.ctorVal.name b.us) b.params) e
  else
    mkProjFn b.ctorVal b.us b.params 0 e

/--
Given a bijection `b` and an expression `e`, return `x` if `e` syntactically matches `b x`.
Returns none if the bijection's parameters don't match syntactically.

If `x` is a `.proj` expression, we WHNF its inferred type, to expose the structure's parameters,
and only then do we compare them syntacticallly.
We might want to make the check less syntactical in the future, but this seems
fine for now. A definitional equality check might be too leanient, so that
`Bijection.mkApp` would cancel too much, and it is more expensive.
-/
private def Bijection.unapply? (b : Bijection) (e : Expr) : MetaM (Option Expr) := do
  if e.isApp then
    let x := e.appArg!
    return if (← b.mkApp x) == e then some x else none
  else if let .proj structName 0 x := e then
    if !b.isCtor && structName == b.ctorVal.induct then
      let xType ← whnfD (← inferType x)
      if xType == mkAppN (mkConst b.ctorVal.induct b.us) b.params then
        return some x
    return none
  else
    return none

/-- Apply `b` to `e`, and if the result is `b (b⁻¹ x)`, simplify it to `x`. -/
protected def Bijection.mkAppAndSimplify (b : Bijection) (e : Expr) : MetaM Expr := do
  if let some x ← b.inv.unapply? e then return x
  b.mkApp e

private def buildBijection? (isCtor : Bool) (structName : Name) (us : List Level)
    (params : Array Expr) :
    MetaM (Option Bijection) := do
  let env ← getEnv
  let some ctorVal := getNonRecStructureCtor? env structName | return none
  if ctorVal.numFields ≠ 1 then return none
  return some { isCtor, ctorVal, us, params }

structure BijectionWrappedFVar where
  fvarId : FVarId
  bijectionsInsideOut : List Bijection

/--
Parses a tower of one-field-structure constructor and projection applications around an fvar
into a `BijectionWrappedFVar` object or returns `none` if parsing fails.
-/
partial def bijectionWrappedFVar? (e : Expr) (outer : List Bijection := []) :
    MetaM (Option BijectionWrappedFVar) := do
  let e := e.consumeMData
  match e with
  | .fvar x =>
    return some ⟨x, outer⟩
  | .proj structName 0 x =>
    let xType ← whnfD (← inferType x)
    let .const _ us := xType.getAppFn | return none
    let some b ← buildBijection? (isCtor := false) structName us xType.getAppArgs
      | return none
    bijectionWrappedFVar? x (b :: outer)
  | .app .. =>
    let .const declName us := e.getAppFn | return none
    let args := e.getAppArgs
    let env ← getEnv
    if let some projInfo := env.getProjectionFnInfo? declName then
      let some ctorVal ← isCtor? projInfo.ctorName | return none
      if args.size ≠ ctorVal.numParams + 1 then return none
      let params := args.extract 0 ctorVal.numParams
      let x := args[ctorVal.numParams]!
      let some b ← buildBijection? (isCtor := false) ctorVal.induct us params
        | return none
      bijectionWrappedFVar? x (b :: outer)
    else if let some ctorVal ← isCtor? declName then
      if args.size ≠ ctorVal.numParams + 1 then return none
      let params := args.extract 0 ctorVal.numParams
      let x := args[ctorVal.numParams]!
      let some b ← buildBijection? (isCtor := true) ctorVal.induct us params
        | return none
      bijectionWrappedFVar? x (b :: outer)
    else
      return none
  | _ =>
    return none

end Lean.Meta.OneFieldStructure
