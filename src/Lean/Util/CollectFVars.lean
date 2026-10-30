/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.LocalContext
public import Lean.Meta.Sym.ExprPtr

public section

namespace Lean.CollectFVars

/--
State of `collectFVars`. It can be threaded through several calls: subterms visited by
earlier calls are not visited again.
Use `{}` for an empty state, and `State.ofFVarSet` for a state that already contains free variables.
-/
structure State where
  /-- Visited subterms, compared by pointer. -/
  private visited : Std.HashSet Meta.Sym.ExprPtr := {}
  fvarSet  : FVarIdSet  := {}
  fvarIds  : Array FVarId := #[]

/--
Returns a state that already contains `fvarSet` and `fvarIds`. Free variables in `fvarSet` are not
collected again, so `fvarSet` can contain variables that are not in `fvarIds`.
-/
def State.ofFVarSet (fvarSet : FVarIdSet) (fvarIds : Array FVarId := #[]) : State :=
  { fvarSet, fvarIds }

instance : EmptyCollection State := ⟨State.ofFVarSet {}⟩
instance : Inhabited State := ⟨{}⟩

def State.add (s : State) (fvarId : FVarId) : State :=
  { s with fvarSet := s.fvarSet.insert fvarId, fvarIds := s.fvarIds.push fvarId }

abbrev Visitor := State → State

mutual
  partial def visit (e : Expr) : Visitor := fun s =>
    if !e.hasFVar || s.visited.contains { expr := e } then s
    else main e { s with visited := s.visited.insert { expr := e } }

  partial def main : Expr → Visitor
    | .proj _ _ e      => visit e
    | .forallE _ d b _ => visit b ∘ visit d
    | .lam _ d b _     => visit b ∘ visit d
    | .letE _ t v b _  => visit b ∘ visit v ∘ visit t
    | .app f a         => visit a ∘ visit f
    | .mdata _ b       => visit b
    -- Equal free variables may be different objects.
    | .fvar fvarId     => fun s => if s.fvarSet.contains fvarId then s else s.add fvarId
    | _                => id
end

end CollectFVars

def collectFVars (s : CollectFVars.State) (e : Expr) : CollectFVars.State :=
  CollectFVars.main e s

end Lean
