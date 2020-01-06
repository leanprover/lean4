/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Expr

namespace Lean

namespace CollectFVars

structure State :=
(visitedExpr  : ExprSet  := {})
(fvarSet      : NameSet  := {})

instance State.inhabited : Inhabited State := ⟨{}⟩

abbrev Visitor := State → State

@[inline] def visit (f : Expr → Visitor) (e : Expr) : Visitor :=
fun s =>
  if !e.hasFVar || s.visitedExpr.contains e then s
  else f e { visitedExpr := s.visitedExpr.insert e, .. s }

partial def main : Expr → Visitor
| Expr.proj _ _ e _    => visit main e
| Expr.forallE _ d b _ => visit main b ∘ visit main d
| Expr.lam _ d b _     => visit main b ∘ visit main d
| Expr.letE _ t v b _  => visit main b ∘ visit main v ∘ visit main t
| Expr.app f a _       => visit main a ∘ visit main f
| Expr.mdata _ b _     => visit main b
| Expr.fvar fvarId _   => fun s => { fvarSet := s.fvarSet.insert fvarId, .. s }
| _                    => id

end CollectFVars

def collectFVars (s : CollectFVars.State) (e : Expr) : CollectFVars.State :=
CollectFVars.main e s

end Lean
