/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.MetavarContext

namespace Lean

/--
  Return true if `e` contains `mvarId` directly or indirectly
  This function considers assigments and delayed assignments. -/
partial def MetavarContext.occursCheck (mctx : MetavarContext) (mvarId : MVarId) (e : Expr) : Bool :=
  match visit e |>.run {} with
  | EStateM.Result.ok ..    => false
  | EStateM.Result.error .. => true
where
  visitMVar (mvarId' : MVarId) : EStateM Unit ExprSet Unit := do
    if mvarId == mvarId' then
      throw () -- found
    else
      match mctx.getExprAssignment? mvarId' with
      | some v => visit v
      | none   =>
        match mctx.getDelayedAssignment? mvarId' with
        | some d => visit d.val
        | none   => return ()

  visit (e : Expr) : EStateM Unit ExprSet Unit := do
    if (← get).contains e then
      return ()
    else
      modify fun s => s.insert e
      match e with
      | Expr.proj _ _ s _    => visit s
      | Expr.forallE _ d b _ => visit d; visit b
      | Expr.lam _ d b _     => visit d; visit b
      | Expr.letE _ t v b _  => visit t; visit v; visit b
      | Expr.mdata _ b _     => visit b
      | Expr.app f a _       => visit f; visit a
      | Expr.mvar mvarId _   => visitMVar mvarId
      | _                    => return ()

end Lean
