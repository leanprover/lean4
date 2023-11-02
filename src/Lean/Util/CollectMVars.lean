/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr

namespace Lean

namespace CollectMVars

structure State where
  visitedExpr  : ExprSet      := {}
  result       : Array MVarId := #[]

instance : Inhabited State := ⟨{}⟩

abbrev Visitor := State → State

mutual
  partial def visit (e : Expr) : Visitor := fun s =>
    if !e.hasMVar || s.visitedExpr.contains e then s
    else main e { s with visitedExpr := s.visitedExpr.insert e }

  partial def main : Expr → Visitor
    | .proj _ _ e      => visit e
    | .forallE _ d b _ => visit b ∘ visit d
    | .lam _ d b _     => visit b ∘ visit d
    | .letE _ t v b    => visit b ∘ visit v ∘ visit t
    | .app f a         => visit a ∘ visit f
    | .mdata _ b       => visit b
    | .mvar mvarId     => fun s => { s with result := s.result.push mvarId }
    | _                => id
end

end CollectMVars

def Expr.collectMVars (s : CollectMVars.State) (e : Expr) : CollectMVars.State :=
  CollectMVars.visit e s

end Lean
