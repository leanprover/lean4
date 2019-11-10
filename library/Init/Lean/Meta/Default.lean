/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.Basic
import Init.Lean.Meta.WHNF
import Init.Lean.Meta.InferType

#exit
/- =========================================== -/
/- BIG HACK until we add `mutual` keyword back -/
/- =========================================== -/
inductive TypeUtilOp
| whnfOp | inferTypeOp | isDefEqOp
open TypeUtilOp
private def exprToBool : Expr → Bool
| Expr.sort Level.zero => false
| _                    => true
private def boolToExpr : Bool → Expr
| false => Expr.sort Level.zero
| true  => Expr.bvar 0

private partial def auxFixpoint [AbstractMetavarContext σ] [AbstractTypeUtilCache ϕ] : TypeUtilOp → Expr → Expr → TypeUtilM σ ϕ Expr
| op, e₁, e₂ =>
  let whnf      := fun e => auxFixpoint whnfOp e e;
  let inferType := fun e => auxFixpoint inferTypeOp e e;
  let isDefEq   := fun e₁ e₂ => exprToBool <$> auxFixpoint isDefEqOp e₁ e₂;
  match op with
  | whnfOp      => whnfAux whnf inferType isDefEq e₁
  | inferTypeOp => inferTypeAux whnf inferType isDefEq e₁
  | isDefEqOp   => boolToExpr <$> isDefEqAux whnf inferType isDefEq e₁ e₂

def whnf [AbstractMetavarContext σ] [AbstractTypeUtilCache ϕ] (e : Expr) : TypeUtilM σ ϕ Expr :=
auxFixpoint whnfOp e e

def inferType [AbstractMetavarContext σ] [AbstractTypeUtilCache ϕ] (e : Expr) : TypeUtilM σ ϕ Expr :=
auxFixpoint inferTypeOp e e

def isDefEq [AbstractMetavarContext σ] [AbstractTypeUtilCache ϕ] (e₁ e₂ : Expr) : TypeUtilM σ ϕ Bool :=
exprToBool <$> auxFixpoint isDefEqOp e₁ e₂
/- =========================================== -/
/-          END OF BIG HACK                    -/
/- =========================================== -/
