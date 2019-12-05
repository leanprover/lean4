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

instance natToExpr : ToExpr Nat := ⟨mkNatLit⟩

instance strToExpr : ToExpr String := ⟨mkStrLit⟩

def nameToExprAux : Name → Expr
| Name.anonymous  => mkConst `Lean.Name.anonymous
| Name.str p s _  => mkAppB (mkConst `Lean.mkNameStr) (nameToExprAux p) (toExpr s)
| Name.num p n _  => mkAppB (mkConst `Lean.mkNameNum) (nameToExprAux p) (toExpr n)

instance nameToExpr : ToExpr Name := ⟨nameToExprAux⟩

end Lean
