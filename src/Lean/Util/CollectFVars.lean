/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr
import Lean.LocalContext

namespace Lean.CollectFVars

structure State where
  visitedExpr  : ExprSet  := {}
  fvarSet      : FVarIdSet  := {}
  fvarIds      : Array FVarId := #[]
  deriving Inhabited

def State.add (s : State) (fvarId : FVarId) : State :=
  { s with fvarSet := s.fvarSet.insert fvarId, fvarIds := s.fvarIds.push fvarId }

abbrev Visitor := State → State

mutual
  partial def visit (e : Expr) : Visitor := fun s =>
    if !e.hasFVar || s.visitedExpr.contains e then s
    else main e { s with visitedExpr := s.visitedExpr.insert e }

  partial def main : Expr → Visitor
    | Expr.proj _ _ e      => visit e
    | Expr.forallE _ d b _ => visit b ∘ visit d
    | Expr.lam _ d b _     => visit b ∘ visit d
    | Expr.letE _ t v b _  => visit b ∘ visit v ∘ visit t
    | Expr.app f a         => visit a ∘ visit f
    | Expr.mdata _ b       => visit b
    | Expr.fvar fvarId     => fun s => s.add fvarId
    | _                    => id
end

partial def collectBackwardDeps (lctx : LocalContext) (i : Nat) : Visitor := fun s =>
  if h : i < s.fvarIds.size then
    let s := if let some ldecl := lctx.find? s.fvarIds[i] then
      visit ldecl.type s
    else
      s
    collectBackwardDeps lctx (i + 1) s
  else
    s

end CollectFVars

def collectFVars (s : CollectFVars.State) (e : Expr) : CollectFVars.State :=
  CollectFVars.main e s

/-- After a call to `collectFVars`, this will close the state under the dependency relation,
meaning that if `v` is in the state and `u` is in the type of `v` then `u` is also in the state. -/
def collectBackwardDeps (s : CollectFVars.State) (lctx : LocalContext) : CollectFVars.State :=
  CollectFVars.collectBackwardDeps lctx 0 s

end Lean
