/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.AppBuilder

namespace Lean.Meta

inductive CongrArgKind where
  | /-- It is a parameter for the congruence theorem, the parameter occurs in the left and right hand sides. -/
    fixed
  | /--
      It is not a parameter for the congruence theorem, the lemma was specialized for this parameter.
      This only happens if the parameter is a subsingleton/proposition, and other parameters depend on it. -/
    fixedNoParam
  | /--
      The lemma contains three parameters for this kind of argument `a_i`, `b_i` and `eq_i : a_i = b_i`.
      `a_i` and `b_i` represent the left and right hand sides, and `eq_i` is a proof for their equality. -/
    eq
  | /--
      The congr-simp theorems contains only one parameter for this kind of argument, and congr theorems contains two.
      They correspond to arguments that are subsingletons/propositions. -/
    cast
  | /--
     The lemma contains three parameters for this kind of argument `a_i`, `b_i` and `eq_i : HEq a_i b_i`.
     `a_i` and `b_i` represent the left and right hand sides, and `eq_i` is a proof for their heterogeneous equality. -/
    heq

structure CongrTheorem where
  type     : Expr
  proof    : Expr
  argKinds : Array CongrArgKind

private def addPrimeToFVarUserNames (ys : Array Expr) (lctx : LocalContext) : LocalContext := do
  let mut lctx := lctx
  for y in ys do
    let decl := lctx.getFVar! y
    lctx := lctx.setUserName decl.fvarId (decl.userName.appendAfter "'")
  return lctx

private def setBinderInfosD (ys : Array Expr) (lctx : LocalContext) : LocalContext := do
  let mut lctx := lctx
  for y in ys do
    let decl := lctx.getFVar! y
    lctx := lctx.setBinderInfo decl.fvarId BinderInfo.default
  return lctx

partial def mkHCongrWithArity (f : Expr) (numArgs : Nat) : MetaM CongrTheorem := do
  let fType ← inferType f
  forallBoundedTelescope fType numArgs fun xs xType =>
  forallBoundedTelescope fType numArgs fun ys yType => do
    if xs.size != numArgs then
      throwError "failed to generate hcongr theorem, insufficient number of arguments"
    else
      let lctx := addPrimeToFVarUserNames ys (← getLCtx) |> setBinderInfosD ys |> setBinderInfosD xs
      withLCtx lctx (← getLocalInstances) do
      withNewEqs xs ys fun eqs argKinds => do
        let mut hs := #[]
        for x in xs, y in ys, eq in eqs do
          hs := hs.push x |>.push y |>.push eq
        let xType := xType.consumeAutoOptParam
        let yType := yType.consumeAutoOptParam
        let resultType ← if xType == yType then mkEq xType yType else mkHEq xType yType
        let congrType ← mkForallFVars hs resultType
        return {
          type  := congrType
          proof := (← mkProof congrType)
          argKinds
        }
where
  withNewEqs {α} (xs ys : Array Expr) (k : Array Expr → Array CongrArgKind → MetaM α) : MetaM α :=
    let rec loop (i : Nat) (eqs : Array Expr) (kinds : Array CongrArgKind) := do
      if  i < xs.size then
        let x := xs[i]
        let y := ys[i]
        let xType := (← inferType x).consumeAutoOptParam
        let yType := (← inferType y).consumeAutoOptParam
        if xType == yType then
          withLocalDeclD ((`e).appendIndexAfter (i+1)) (← mkEq x y) fun h =>
            loop (i+1) (eqs.push h) (kinds.push CongrArgKind.eq)
        else
          withLocalDeclD ((`e).appendIndexAfter (i+1)) (← mkHEq x y) fun h =>
            loop (i+1) (eqs.push h) (kinds.push CongrArgKind.heq)
      else
        k eqs kinds
    loop 0 #[] #[]

  mkProof (type : Expr) : MetaM Expr := do
    if let some (_, lhs, _) := type.eq? then
      mkEqRefl lhs
    else if let some (_, lhs, _, _) := type.heq? then
      mkHEqRefl lhs
    else
      forallBoundedTelescope type (some 1) fun a type =>
      let a := a[0]
      forallBoundedTelescope type (some 1) fun b motive =>
      let b := b[0]
      let type := type.bindingBody!.instantiate1 a
      withLocalDeclD motive.bindingName! motive.bindingDomain! fun eqPr => do
      let type := type.bindingBody!
      let motive := motive.bindingBody!
      let minor ← mkProof type
      let mut major := eqPr
      if (← whnf (← inferType eqPr)).isHEq then
        major ← mkEqOfHEq major
      let motive ← mkLambdaFVars #[b] motive
      mkLambdaFVars #[a, b, eqPr] (← mkEqNDRec motive minor major)

def mkHCongr (f : Expr) : MetaM CongrTheorem := do
  mkHCongrWithArity f (← getFunInfo f).getArity

end Lean.Meta
