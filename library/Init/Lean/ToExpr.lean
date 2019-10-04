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
(toExpr : α → Expr)

export ToExpr (toExpr)

instance exprToExpr : ToExpr Expr := ⟨id⟩

instance natToExpr : ToExpr Nat := ⟨fun n => Expr.lit (Literal.natVal n)⟩

instance strToExpr : ToExpr String := ⟨fun s => Expr.lit (Literal.strVal s)⟩

def nameToExprAux : Name → Expr
| Name.anonymous     => mkConst `Lean.Name.anonymous
| Name.mkString p s  => mkBinCApp `Lean.Name.mkString (nameToExprAux p) (toExpr s)
| Name.mkNumeral p n => mkBinCApp `Lean.Name.mkNumeral (nameToExprAux p) (toExpr n)

instance nameToExpr : ToExpr Name := ⟨nameToExprAux⟩

end Lean
