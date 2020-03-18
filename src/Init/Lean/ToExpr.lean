/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Expr
universe u

namespace Lean

class ToExpr (α : Type u) :=
(toExpr     : α → Expr)
(toTypeExpr : Expr)

export ToExpr (toExpr toTypeExpr)

instance exprToExpr : ToExpr Expr :=
{ toExpr     := id,
  toTypeExpr := mkConst `Expr }

instance natToExpr : ToExpr Nat :=
{ toExpr     := mkNatLit,
  toTypeExpr := mkConst `Nat }

instance boolToExpr : ToExpr Bool :=
{ toExpr     := fun b => if b then mkConst `Bool.true else mkConst `Bool.false,
  toTypeExpr := mkConst `Bool }

instance charToExpr : ToExpr Char :=
{ toExpr     := fun c => mkApp (mkConst `Char.ofNat) (toExpr c.toNat),
  toTypeExpr := mkConst `Char }

instance strToExpr : ToExpr String :=
{ toExpr     := mkStrLit,
  toTypeExpr := mkConst `String }

instance unitToExpr : ToExpr Unit :=
{ toExpr     := fun _ => mkConst `Unit.unit,
  toTypeExpr := mkConst `Unit }

def Name.toExprAux : Name → Expr
| Name.anonymous  => mkConst `Lean.Name.anonymous
| Name.str p s _  => mkAppB (mkConst `Lean.mkNameStr) (Name.toExprAux p) (toExpr s)
| Name.num p n _  => mkAppB (mkConst `Lean.mkNameNum) (Name.toExprAux p) (toExpr n)

instance nameToExpr : ToExpr Name :=
{ toExpr     := Name.toExprAux,
  toTypeExpr := mkConst `Name }

def List.toExprAux {α} [ToExpr α] (nilFn : Expr) (consFn : Expr) : List α → Expr
| []    => nilFn
| a::as => mkApp2 consFn (toExpr a) (List.toExprAux as)

instance listToExpr {α : Type} [ToExpr α] : ToExpr (List α) :=
let type := toTypeExpr α;
let nil  := mkApp (mkConst `List.nil [levelZero]) type;
let cons := mkApp (mkConst `List.cons [levelZero]) type;
{ toExpr     := List.toExprAux nil cons,
  toTypeExpr := mkApp (mkConst `List [levelZero]) type }

instance arrayToExpr {α : Type} [ToExpr α] : ToExpr (Array α) :=
let type := toTypeExpr α;
{ toExpr     := fun as => mkApp2 (mkConst `List.toArray [levelZero]) type (toExpr as.toList),
  toTypeExpr := mkApp (mkConst `Array [levelZero]) type }

instance prodToExpr {α : Type} {β : Type} [ToExpr α] [ToExpr β] : ToExpr (α × β) :=
let αType := toTypeExpr α;
let βType := toTypeExpr β;
{ toExpr     := fun ⟨a, b⟩ => mkApp4 (mkConst `Prod.mk [levelZero, levelZero]) αType βType (toExpr a) (toExpr b),
  toTypeExpr := mkApp2 (mkConst `Prod [levelZero, levelZero]) αType βType }

end Lean
