/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Expr

namespace Lean

namespace CollectLevelParams

structure State :=
(visitedLevel : LevelSet   := {})
(visitedExpr  : ExprSet    := {})
(params       : Array Name := #[])

instance State.inhabited : Inhabited State := ⟨{}⟩

abbrev Visitor := State → State

@[inline] def visitLevel (f : Level → Visitor) (u : Level) : Visitor :=
fun s =>
  if !u.hasParam || s.visitedLevel.contains u then s
  else f u { visitedLevel := s.visitedLevel.insert u, .. s }

partial def collect : Level → Visitor
| Level.succ v _    => visitLevel collect v
| Level.max u v _   => visitLevel collect v ∘ visitLevel collect u
| Level.imax u v _  => visitLevel collect v ∘ visitLevel collect u
| Level.param n _   => fun s => { params := s.params.push n, .. s }
| _                 => id

@[inline] def visitExpr (f : Expr → Visitor) (e : Expr) : Visitor :=
fun s =>
  if !e.hasLevelParam then s
  else if s.visitedExpr.contains e then s
  else f e { visitedExpr := s.visitedExpr.insert e, .. s }

partial def main : Expr → Visitor
| Expr.proj _ _ s _    => visitExpr main s
| Expr.forallE _ d b _ => visitExpr main b ∘ visitExpr main d
| Expr.lam _ d b _     => visitExpr main b ∘ visitExpr main d
| Expr.letE _ t v b _  => visitExpr main b ∘ visitExpr main v ∘ visitExpr main t
| Expr.app f a _       => visitExpr main a ∘ visitExpr main f
| Expr.mdata _ b _     => visitExpr main b
| Expr.const _ us _    => fun s => us.foldl (fun s u => visitLevel collect u s) s
| Expr.sort u _        => visitLevel collect u
| _                    => id

end CollectLevelParams

def collectLevelParams (s : CollectLevelParams.State) (e : Expr) : CollectLevelParams.State :=
CollectLevelParams.main e s

end Lean
