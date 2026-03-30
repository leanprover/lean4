/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Expr

public section

namespace Lean

namespace CollectMVars

structure State where
  visitedExpr  : ExprSet      := {}
  result       : Array MVarId := #[]

instance : Inhabited State := ⟨{}⟩

abbrev Visitor := State → State

mutual
  partial def visit (e : Expr) : Visitor := fun s =>
    if !e.hasExprMVar || s.visitedExpr.contains e then s
    else main e { s with visitedExpr := s.visitedExpr.insert e }

  partial def main : Expr → Visitor
    | Expr.proj _ _ e      => visit e
    | Expr.forallE _ d b _ => visit b ∘ visit d
    | Expr.lam _ d b _     => visit b ∘ visit d
    | Expr.letE _ t v b _  => visit b ∘ visit v ∘ visit t
    | Expr.app f a         => visit a ∘ visit f
    | Expr.mdata _ b       => visit b
    | Expr.mvar mvarId     => fun s => { s with result := s.result.push mvarId }
    | _                    => id
end

end CollectMVars

def Expr.collectMVars (s : CollectMVars.State) (e : Expr) : CollectMVars.State :=
  CollectMVars.visit e s

namespace CollectBothMVars

structure State where
  visitedLevel : LevelSet      := {}
  visitedExpr  : ExprSet       := {}
  mvars        : Array MVarId  := #[]
  lmvars       : Array LMVarId := #[]

instance : Inhabited State := ⟨{}⟩

abbrev Visitor := State → State

mutual
  partial def visitLevel (u : Level) : Visitor := fun s =>
    if !u.hasMVar || s.visitedLevel.contains u then s
    else mainLevel u { s with visitedLevel := s.visitedLevel.insert u }

  partial def mainLevel : Level → Visitor
    | .succ v    => visitLevel v
    | .max u v   => visitLevel v ∘ visitLevel u
    | .imax u v  => visitLevel v ∘ visitLevel u
    | .mvar m    => fun s => { s with lmvars := s.lmvars.push m }
    | _          => id
end

mutual
  partial def visitExpr (e : Expr) : Visitor := fun s =>
    if !e.hasMVar then s
    else if s.visitedExpr.contains e then s
    else mainExpr e { s with visitedExpr := s.visitedExpr.insert e }

  partial def mainExpr : Expr → Visitor
    | .proj _ _ s      => visitExpr s
    | .forallE _ d b _ => visitExpr b ∘ visitExpr d
    | .lam _ d b _     => visitExpr b ∘ visitExpr d
    | .letE _ t v b _  => visitExpr b ∘ visitExpr v ∘ visitExpr t
    | .app f a         => visitExpr a ∘ visitExpr f
    | .mdata _ b       => visitExpr b
    | .const _ us      => us.foldl (fun s u => visitLevel u s)
    | .sort u          => visitLevel u
    | .mvar mvarId     => fun s => { s with mvars := s.mvars.push mvarId }
    | _                => id
end

end CollectBothMVars

def Expr.collectBothMVars (s : CollectBothMVars.State) (e : Expr) : CollectBothMVars.State :=
  CollectBothMVars.visitExpr e s

end Lean
