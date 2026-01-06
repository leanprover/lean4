/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Basic
import Lean.Meta.InferType
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
  withLocalDeclD `f type fun f =>
  withLocalDeclD `g type fun g => do
  let lhs := mkAppN f xs
  let rhs := mkAppN g xs
  let p := mkApp3 (mkConst ``Eq [v]) β lhs rhs
  let p ← mkForallFVars xs p
  withLocalDeclD `h p fun h => do
  let mut result := mkAppN h xs |>.abstract xs
  let mut i := xs.size
  let mut β := β.abstract xs
  let mut v := v
  let mut f := mkAppN f xs |>.abstract xs
  let mut g := mkAppN g xs |>.abstract xs
  while i > 0 do
    i := i - 1
    let x := xs[i]!
    let α_i ← inferType x
    let u_i ← getLevel α_i
    let α_i := α_i.abstractRange i xs
    f := f.appFn!.lowerLooseBVars 1 1
    g := g.appFn!.lowerLooseBVars 1 1
    result := mkLambda `x default α_i result
    result := mkApp5 (mkConst ``funext [u_i, v]) α_i (mkLambda `x .default α_i β) f g result
    β := mkForall `x .default α_i β
    v := mkLevelIMax' u_i v
  mkLambdaFVars #[f, g, h] result

end Lean.Meta.Sym.Simp
