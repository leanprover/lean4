/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.Expr

namespace Lean

namespace CollectLevelMVars

structure State where
  visitedLevel : LevelSet      := {}
  visitedExpr  : ExprSet       := {}
  result       : Array LMVarId := {}

instance : Inhabited State := ⟨{}⟩

abbrev Visitor := State → State

mutual
  partial def visitLevel (u : Level) : Visitor := fun s =>
    if !u.hasMVar || s.visitedLevel.contains u then s
    else collect u { s with visitedLevel := s.visitedLevel.insert u }

  partial def collect : Level → Visitor
    | .succ v    => visitLevel v
    | .max u v   => visitLevel v ∘ visitLevel u
    | .imax u v  => visitLevel v ∘ visitLevel u
    | .mvar m    => fun s => { s with result := s.result.push m }
    | _          => id
end

mutual
  partial def visitExpr (e : Expr) : Visitor := fun s =>
    if !e.hasMVar then s
    else if s.visitedExpr.contains e then s
    else main e { s with visitedExpr := s.visitedExpr.insert e }

  partial def main : Expr → Visitor
    | .proj _ _ s      => visitExpr s
    | .forallE _ d b _ => visitExpr b ∘ visitExpr d
    | .lam _ d b _     => visitExpr b ∘ visitExpr d
    | .letE _ t v b _  => visitExpr b ∘ visitExpr v ∘ visitExpr t
    | .app f a         => visitExpr a ∘ visitExpr f
    | .mdata _ b       => visitExpr b
    | .const _ us      => us.foldl (fun s u => visitLevel u s)
    | .sort u          => visitLevel u
    | _                => id
end

end CollectLevelMVars

/--
Collects all universe level metavariables present in `e`.
Result is in `Lean.CollectLevelMVars.State.result`.
-/
def collectLevelMVars (s : CollectLevelMVars.State) (e : Expr) : CollectLevelMVars.State :=
  CollectLevelMVars.main e s

end Lean
