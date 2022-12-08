/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr

namespace Lean

namespace FindMVar

abbrev Visitor := Option MVarId → Option MVarId

mutual
  partial def visit (p : MVarId → Bool) (e : Expr) : Visitor := fun s =>
    if s.isSome || !e.hasMVar then s else main p e s

  partial def main (p : MVarId → Bool) : Expr → Visitor
    | Expr.proj _ _ e      => visit p e
    | Expr.forallE _ d b _ => visit p b ∘ visit p d
    | Expr.lam _ d b _     => visit p b ∘ visit p d
    | Expr.letE _ t v b _  => visit p b ∘ visit p v ∘ visit p t
    | Expr.app f a         => visit p a ∘ visit p f
    | Expr.mdata _ b       => visit p b
    | Expr.mvar mvarId     => fun s => if s.isNone && p mvarId then some mvarId else s
    | _                    => id
end

end FindMVar

@[inline] def Expr.findMVar? (e : Expr) (p : MVarId → Bool) : Option MVarId :=
  FindMVar.main p e none

end Lean
