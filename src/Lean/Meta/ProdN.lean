/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/

module

prelude
public import Lean.Meta.InferType
import Lean.Meta.DecLevel

public section

namespace Lean.Meta

/--
Given types `tᵢ`, return the tuple type `t₁ × t₂ × … × tₙ`.
For `n = 0`, return `PUnit` with the given level + 1.
-/
def mkProdN (ts : Array Expr) (u : Level /- used as `Type u` -/) : MetaM Expr := do
  if h : ts.size > 0 then
    let mut tupleTy := ts.back
    let mut u ← getDecLevel tupleTy
    let mut ts := ts.pop
    for i in 0...ts.size do
      let ty := ts.back!
      let u' ← getDecLevel ty
      tupleTy := mkApp2 (mkConst ``Prod [u', u]) ty tupleTy
      u := (mkLevelMax u u').normalize
      ts := ts.pop
    return tupleTy
  else
    return mkConst ``PUnit [mkLevelSucc u]

/--
Given expressions `eᵢ`, return the tuple `(e₁, e₂, …, eₙ)` and its type `t₁ × t₂ × … × tₙ`.
For `n = 0`, return `PUnit.unit` with the given level + 1.
-/
def mkProdMkN (es : Array Expr) (u : Level /- used as `Type u` -/) : MetaM (Expr × Expr) := do
  if h : es.size > 0 then
    let mut tuple := es.back
    let mut tupleTy ← inferType tuple
    let mut u ← getDecLevel tupleTy
    let mut es := es.pop
    for i in 0...es.size do
      let e := es.back!
      let ty ← inferType e
      let u' ← getDecLevel ty
      tuple := mkApp4 (mkConst ``Prod.mk [u', u]) ty tupleTy e tuple
      tupleTy := mkApp2 (mkConst ``Prod [u', u]) ty tupleTy
      u := (mkLevelMax u u').normalize
      es := es.pop
    return (tuple, tupleTy)
  else
    return (mkConst ``PUnit.unit [mkLevelSucc u], mkConst ``PUnit [mkLevelSucc u])

/-- Given a product `(e₁, e₂)` of type `t₁ × t₂`, return `(e₁, t₁, e₂, t₂)`. -/
def getProdFields (tuple tupleTy : Expr) : MetaM (Expr × Expr × Expr × Expr) := do
  let tupleTy ← instantiateMVarsIfMVarApp tupleTy
  let_expr c@Prod fstTy sndTy := tupleTy
    | throwError "Internal error: Expected Prod, got {tuple} of type {tupleTy}"
  let fst := mkApp3 (mkConst ``Prod.fst c.constLevels!) fstTy sndTy tuple
  let snd := mkApp3 (mkConst ``Prod.snd c.constLevels!) fstTy sndTy tuple
  return (fst, fstTy, snd, sndTy)
