/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Closure
namespace Lean.Meta.Sym.Simp

/--
Given `xs` containing free variables
`(x₁ : α₁) (x₂ : α₂[x₁]) ... (xₙ : αₙ[x₁, ..., x_{n-1}])`
and `β` a type of the form `β[x₁, ..., xₙ]`,
creates the custom function extensionality theorem
```
∀ (f g : (x₁ : α₁) → (x₂ : α₂[x₁]) → ... → (xₙ : αₙ[x₁, ..., x_{n-1}]) → β[x₁, ..., xₙ])
  (h : ∀ x₁ ... xₙ, f x₁ ... xₙ = g x₁ ... xₙ),
  f = g
```
The theorem has three arguments `f`, `g`, and `h`.
This auxiliary theorem is used by the simplifier when visiting lambda expressions.
-/
def mkFunextFor (xs : Array Expr) (β : Expr) : MetaM Expr := do
  let type ← mkForallFVars xs β
  let v ← getLevel β
  let w ← getLevel type
  withLocalDeclD `f type fun f =>
  withLocalDeclD `g type fun g => do
  let eq := mkApp3 (mkConst ``Eq [v]) β (mkAppN f xs) (mkAppN g xs)
  withLocalDeclD `h (← mkForallFVars xs eq) fun h => do
  let eqv ← mkLambdaFVars #[f, g] (← mkForallFVars xs eq)
  let quotEqv := mkApp2 (mkConst ``Quot [w]) type eqv
  withLocalDeclD `f' quotEqv fun f' => do
  let lift := mkApp6 (mkConst ``Quot.lift [w, v]) type eqv β
    (mkLambda `f .default type (mkAppN (.bvar 0) xs))
    (mkLambda `f .default type (mkLambda `g .default type (mkLambda `h .default (mkApp2 eqv (.bvar 1) (.bvar 0)) (mkAppN (.bvar 0) xs))))
    f'
  let extfunAppVal ← mkLambdaFVars (#[f'] ++ xs) lift
  let extfunApp := extfunAppVal
  let quotSound := mkApp5 (mkConst ``Quot.sound [w]) type eqv f g h
  let Quot_mk_f := mkApp3 (mkConst ``Quot.mk [w]) type eqv f
  let Quot_mk_g := mkApp3 (mkConst ``Quot.mk [w]) type eqv g
  let result := mkApp6 (mkConst ``congrArg [w, w]) quotEqv type Quot_mk_f Quot_mk_g extfunApp quotSound
  let result ← mkLambdaFVars #[f, g, h] result
  return result

public def simpLambda (e : Expr) : SimpM Result := do
  lambdaTelescope e fun xs b => withoutModifyingCacheIfNotWellBehaved do
    main xs b
where
  main (xs : Array Expr) (b : Expr) : SimpM Result := do
    match (← simp b) with
    | .rfl _ => return .rfl
    | .step b' h _ =>
      let h ← mkLambdaFVars xs h
      let e' ← shareCommonInc (← mkLambdaFVars xs b')
      let funext ← getFunext xs b
      return .step e' (mkApp3 funext e e' h)

  getFunext (xs : Array Expr) (b : Expr) : SimpM Expr := do
    let key ← inferType e
    if let some h := (← get).funext.find? { expr := key } then
      return h
    else
      let β ← inferType b
      let h ← mkFunextFor xs β
      modify fun s => { s with funext := s.funext.insert { expr := key } h }
      return h

end Lean.Meta.Sym.Simp
