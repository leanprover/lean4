/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr
universe u

namespace Lean

/--
We use the `ToExpr` type class to convert values of type `α` into
expressions that denote these values in Lean.
Example:
```
toExpr true = .const ``Bool.true []
```
-/
class ToExpr (α : Type u) where
  /-- Convert a value `a : α` into an expression that denotes `a` -/
  toExpr     : α → Expr
  /-- Expression representing the type `α` -/
  toTypeExpr : Expr

export ToExpr (toExpr toTypeExpr)

instance : ToExpr Nat where
  toExpr     := mkNatLit
  toTypeExpr := mkConst ``Nat

instance : ToExpr Bool where
  toExpr     := fun b => if b then mkConst ``Bool.true else mkConst ``Bool.false
  toTypeExpr := mkConst ``Bool

instance : ToExpr Char where
  toExpr     := fun c => mkApp (mkConst ``Char.ofNat) (toExpr c.toNat)
  toTypeExpr := mkConst ``Char

instance : ToExpr String where
  toExpr     := mkStrLit
  toTypeExpr := mkConst ``String

instance : ToExpr Unit where
  toExpr     := fun _ => mkConst `Unit.unit
  toTypeExpr := mkConst ``Unit

private def Name.toExprAux : Name → Expr
  | .anonymous => mkConst ``Lean.Name.anonymous
  | .str p s ..=> mkApp2 (mkConst ``Lean.Name.str) (toExprAux p) (toExpr s)
  | .num p n ..=> mkApp2 (mkConst ``Lean.Name.num) (toExprAux p) (toExpr n)

instance : ToExpr Name where
  toExpr     := Name.toExprAux
  toTypeExpr := mkConst ``Name

instance [ToExpr α] : ToExpr (Option α) :=
  let type := toTypeExpr α
  { toExpr     := fun o => match o with
      | none   => mkApp (mkConst ``Option.none [levelZero]) type
      | some a => mkApp2 (mkConst ``Option.some [levelZero]) type (toExpr a),
    toTypeExpr := mkApp (mkConst ``Option [levelZero]) type }

private def List.toExprAux [ToExpr α] (nilFn : Expr) (consFn : Expr) : List α → Expr
  | []    => nilFn
  | a::as => mkApp2 consFn (toExpr a) (toExprAux nilFn consFn as)

instance [ToExpr α] : ToExpr (List α) :=
  let type := toTypeExpr α
  let nil  := mkApp (mkConst ``List.nil [levelZero]) type
  let cons := mkApp (mkConst ``List.cons [levelZero]) type
  { toExpr     := List.toExprAux nil cons,
    toTypeExpr := mkApp (mkConst ``List [levelZero]) type }

instance [ToExpr α] : ToExpr (Array α) :=
  let type := toTypeExpr α
  { toExpr     := fun as => mkApp2 (mkConst ``List.toArray [levelZero]) type (toExpr as.toList),
    toTypeExpr := mkApp (mkConst ``Array [levelZero]) type }

instance [ToExpr α] [ToExpr β] : ToExpr (α × β) :=
  let αType := toTypeExpr α
  let βType := toTypeExpr β
  { toExpr     := fun ⟨a, b⟩ => mkApp4 (mkConst ``Prod.mk [levelZero, levelZero]) αType βType (toExpr a) (toExpr b),
    toTypeExpr := mkApp2 (mkConst ``Prod [levelZero, levelZero]) αType βType }

end Lean
