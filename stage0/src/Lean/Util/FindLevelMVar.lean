/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Selsam
-/
import Lean.Expr

namespace Lean

namespace FindLevelMVar

abbrev Visitor := Option LMVarId → Option LMVarId

mutual
  partial def visit (p : LMVarId → Bool) (e : Expr) : Visitor := fun s =>
    if s.isSome || !e.hasLevelMVar then s else main p e s

  partial def main (p : LMVarId → Bool) : Expr → Visitor
    | .sort l          => visitLevel p l
    | .const _ ls      => ls.foldr (init := id) fun l acc => visitLevel p l ∘ acc
    | .forallE _ d b _ => visit p b ∘ visit p d
    | .lam _ d b _     => visit p b ∘ visit p d
    | .letE _ t v b _  => visit p b ∘ visit p v ∘ visit p t
    | .app f a         => visit p a ∘ visit p f
    | .mdata _ b       => visit p b
    | .proj _ _ e      => visit p e
    | _                    => id

  partial def visitLevel (p : LMVarId → Bool) (l : Level) : Visitor := fun s =>
    if s.isSome || !l.hasMVar then s else mainLevel p l s

  partial def mainLevel (p : LMVarId → Bool) : Level → Visitor
    | .zero        => id
    | .succ l      => visitLevel p l
    | .max l₁ l₂   => visitLevel p l₁ ∘ visitLevel p l₂
    | .imax l₁ l₂  => visitLevel p l₁ ∘ visitLevel p l₂
    | .param _     => id
    | .mvar mvarId => fun s => if p mvarId then some mvarId else s
end

end FindLevelMVar

@[inline] def Expr.findLevelMVar? (e : Expr) (p : LMVarId → Bool) : Option LMVarId :=
  FindLevelMVar.main p e none

end Lean
