/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean.Expr

namespace Lean

namespace FindLevelMVar

abbrev Visitor := Option MVarId → Option MVarId

mutual
  partial def visit (p : MVarId → Bool) (e : Expr) : Visitor := fun s =>
    if s.isSome || !e.hasLevelMVar then s else main p e s

  @[specialize]
  partial def main (p : MVarId → Bool) : Expr → Visitor
    | Expr.sort l _        => visitLevel p l
    | Expr.const _ ls _    => ls.foldr (init := id) fun l acc => visitLevel p l ∘ acc
    | Expr.forallE _ d b _ => visit p b ∘ visit p d
    | Expr.lam _ d b _     => visit p b ∘ visit p d
    | Expr.letE _ t v b _  => visit p b ∘ visit p v ∘ visit p t
    | Expr.app f a _       => visit p a ∘ visit p f
    | Expr.mdata _ b _     => visit p b
    | Expr.proj _ _ e _    => visit p e
    | _                    => id

  partial def visitLevel (p : MVarId → Bool) (l : Level) : Visitor := fun s =>
    if s.isSome || !l.hasMVar then s else mainLevel p l s

  @[specialize]
  partial def mainLevel (p : MVarId → Bool) : Level → Visitor
    | Level.zero _        => id
    | Level.succ l _      => visitLevel p l
    | Level.max l₁ l₂ _   => visitLevel p l₁ ∘ visitLevel p l₂
    | Level.imax l₁ l₂ _  => visitLevel p l₁ ∘ visitLevel p l₂
    | Level.param n _     => id
    | Level.mvar mvarId _ => fun s => if p mvarId then some mvarId else s
end

end FindLevelMVar

@[inline] def Expr.findLevelMVar? (e : Expr) (p : MVarId → Bool) : Option MVarId :=
  FindLevelMVar.main p e none

end Lean
