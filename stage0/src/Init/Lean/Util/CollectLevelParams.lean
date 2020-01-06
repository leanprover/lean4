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

abbrev M := StateM State

@[inline] def visitLevel (f : Level → M Unit) (u : Level) : M Unit :=
if !u.hasParam then pure ()
else do
  s ← get;
  if s.visitedLevel.contains u then pure ()
  else do
    modify $ fun s => { visitedLevel := s.visitedLevel.insert u, .. s };
    f u

partial def collect : Level → M Unit
| Level.succ v _    => visitLevel collect v
| Level.max u v _   => do visitLevel collect u; visitLevel collect v
| Level.imax u v _  => do visitLevel collect u; visitLevel collect v
| Level.param n _   => modify $ fun s => { params := s.params.push n, .. s }
| _                 => pure ()

@[inline] def visitExpr (f : Expr → M Unit) (e : Expr) : M Unit :=
if !e.hasLevelParam then pure ()
else do
  s ← get;
  if s.visitedExpr.contains e then pure ()
  else do
    modify $ fun s => { visitedExpr := s.visitedExpr.insert e, .. s };
    f e

partial def main : Expr → M Unit
| Expr.proj _ _ s _    => visitExpr main s
| Expr.forallE _ d b _ => do visitExpr main d; visitExpr main b
| Expr.lam _ d b _     => do visitExpr main d; visitExpr main b
| Expr.letE _ t v b _  => do visitExpr main t; visitExpr main v; visitExpr main b
| Expr.app f a _       => do visitExpr main f; visitExpr main a
| Expr.mdata _ b _     => visitExpr main b
| Expr.const _ us _    => us.forM (visitLevel collect)
| Expr.sort u _        => visitLevel collect u
| _                    => pure ()

end CollectLevelParams

def collectLevelParams (e : Expr) : Array Name :=
(CollectLevelParams.main e {}).2.params

end Lean
