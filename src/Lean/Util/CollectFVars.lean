/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr

namespace Lean.CollectFVars

structure State where
  visitedExpr  : ExprSet  := {}
  fvarSet      : FVarIdSet  := {}
  deriving Inhabited

abbrev Visitor := State → State

mutual
  partial def visit (e : Expr) : Visitor := fun s =>
    if !e.hasFVar || s.visitedExpr.contains e then s
    else main e { s with visitedExpr := s.visitedExpr.insert e }

  partial def main : Expr → Visitor
    | Expr.proj _ _ e _    => visit e
    | Expr.forallE _ d b _ => visit b ∘ visit d
    | Expr.lam _ d b _     => visit b ∘ visit d
    | Expr.letE _ t v b _  => visit b ∘ visit v ∘ visit t
    | Expr.app f a _       => visit a ∘ visit f
    | Expr.mdata _ b _     => visit b
    | Expr.fvar fvarId _   => fun s => { s with fvarSet := s.fvarSet.insert fvarId }
    | _                    => id
end

end CollectFVars

def collectFVars (s : CollectFVars.State) (e : Expr) : CollectFVars.State :=
  CollectFVars.main e s

end Lean
