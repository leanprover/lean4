/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Basic
import Lean.Meta.InferType
import Lean.Meta.Closure
import Lean.Meta.AppBuilder
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
public def mkFunextFor (xs : Array Expr) (β : Expr) : MetaM Expr := do
  let type ← mkForallFVars xs β
  let v ← getLevel β
  let w ← getLevel type
  withLocalDeclD `f type fun f =>
  withLocalDeclD `g type fun g => do
  let lhs := mkAppN f xs
  let rhs := mkAppN g xs
  let eq := mkApp3 (mkConst ``Eq [v]) β lhs rhs
  let p ← mkForallFVars xs eq
  withLocalDeclD `h p fun h => do
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

end Lean.Meta.Sym.Simp
