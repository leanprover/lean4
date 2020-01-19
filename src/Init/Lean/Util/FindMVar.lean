/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Expr

namespace Lean

namespace FindMVar

abbrev Visitor := Option MVarId → Option MVarId

@[inline] def visit (f : Expr → Visitor) (e : Expr) : Visitor :=
fun s => if s.isSome || !e.hasMVar then s else f e s

@[specialize] partial def main (p : MVarId → Bool) : Expr → Visitor
| Expr.proj _ _ e _    => visit main e
| Expr.forallE _ d b _ => visit main b ∘ visit main d
| Expr.lam _ d b _     => visit main b ∘ visit main d
| Expr.letE _ t v b _  => visit main b ∘ visit main v ∘ visit main t
| Expr.app f a _       => visit main a ∘ visit main f
| Expr.mdata _ b _     => visit main b
| Expr.mvar mvarId _   => fun s => if s.isNone && p mvarId then some mvarId else s
| _                    => id

end FindMVar

@[inline] def Expr.findMVar? (e : Expr) (p : MVarId → Bool) : Option MVarId :=
FindMVar.main p e none

end Lean
