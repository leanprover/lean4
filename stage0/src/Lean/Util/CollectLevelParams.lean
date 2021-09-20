/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr

namespace Lean

namespace CollectLevelParams

structure State where
  visitedLevel : LevelSet   := {}
  visitedExpr  : ExprSet    := {}
  params       : Array Name := #[]

instance : Inhabited State := ⟨{}⟩

abbrev Visitor := State → State

mutual
  partial def visitLevel (u : Level) : Visitor := fun s =>
    if !u.hasParam || s.visitedLevel.contains u then s
    else collect u { s with visitedLevel := s.visitedLevel.insert u }

  partial def collect : Level → Visitor
    | Level.succ v _    => visitLevel v
    | Level.max u v _   => visitLevel v ∘ visitLevel u
    | Level.imax u v _  => visitLevel v ∘ visitLevel u
    | Level.param n _   => fun s => { s with params := s.params.push n }
    | _                 => id
end

mutual
  partial def visitExpr (e : Expr) : Visitor := fun s =>
    if !e.hasLevelParam then s
    else if s.visitedExpr.contains e then s
    else main e { s with visitedExpr := s.visitedExpr.insert e }

  partial def main : Expr → Visitor
    | Expr.proj _ _ s _    => visitExpr s
    | Expr.forallE _ d b _ => visitExpr b ∘ visitExpr d
    | Expr.lam _ d b _     => visitExpr b ∘ visitExpr d
    | Expr.letE _ t v b _  => visitExpr b ∘ visitExpr v ∘ visitExpr t
    | Expr.app f a _       => visitExpr a ∘ visitExpr f
    | Expr.mdata _ b _     => visitExpr b
    | Expr.const _ us _    => fun s => us.foldl (fun s u => visitLevel u s) s
    | Expr.sort u _        => visitLevel u
    | _                    => id
end

partial def State.getUnusedLevelParam (s : CollectLevelParams.State) (pre : Name := `v) : Level :=
  let v := mkLevelParam pre;
  if s.visitedLevel.contains v then
    let rec loop (i : Nat) :=
      let v := mkLevelParam (pre.appendIndexAfter i);
      if s.visitedLevel.contains v then loop (i+1) else v
    loop 1
  else
    v

end CollectLevelParams

def collectLevelParams (s : CollectLevelParams.State) (e : Expr) : CollectLevelParams.State :=
  CollectLevelParams.main e s

def CollectLevelParams.State.collect (s : CollectLevelParams.State) (e : Expr) : CollectLevelParams.State :=
  collectLevelParams s e

end Lean
