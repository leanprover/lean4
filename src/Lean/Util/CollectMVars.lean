/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Expr
public import Lean.Meta.Sym.ExprPtr

public section

namespace Lean

namespace CollectMVars

/--
State of `Expr.collectMVars`. It can be threaded through several calls: subterms visited by
earlier calls are not visited again. Use `{}` for an empty state.
-/
structure State where
  /-- Visited subterms, compared by pointer. -/
  private visited : Std.HashSet Meta.Sym.ExprPtr := {}
  /-- Metavariables in `result`. -/
  private mvarSet : MVarIdSet := {}
  result       : Array MVarId := #[]

def State.empty : State := {}

instance : EmptyCollection State := ⟨State.empty⟩
instance : Inhabited State := ⟨{}⟩

abbrev Visitor := State → State

mutual
  partial def visit (e : Expr) : Visitor := fun s =>
    if !e.hasExprMVar || s.visited.contains { expr := e } then s
    else main e { s with visited := s.visited.insert { expr := e } }

  partial def main : Expr → Visitor
    | Expr.proj _ _ e      => visit e
    | Expr.forallE _ d b _ => visit b ∘ visit d
    | Expr.lam _ d b _     => visit b ∘ visit d
    | Expr.letE _ t v b _  => visit b ∘ visit v ∘ visit t
    | Expr.app f a         => visit a ∘ visit f
    | Expr.mdata _ b       => visit b
    -- Equal metavariables may be different objects.
    | Expr.mvar mvarId     => fun s =>
      if s.mvarSet.contains mvarId then s
      else { s with mvarSet := s.mvarSet.insert mvarId, result := s.result.push mvarId }
    | _                    => id
end

end CollectMVars

def Expr.collectMVars (s : CollectMVars.State) (e : Expr) : CollectMVars.State :=
  CollectMVars.visit e s

end Lean
