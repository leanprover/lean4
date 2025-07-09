/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.Expr

/-!
# Folding over the loose bound variables in an expression.

This module provides a function for folding over the loose bvars in an expression.
This means finding the set of `i` for which `e.hasLooseBVar i` is true and folding the function over all such `i`.
-/

namespace Lean.Expr

namespace FoldLooseBVars

structure State (α : Type) where
  value : α
  visited : Std.HashSet (Nat × Expr) := {}

abbrev M (α : Type) := StateM (State α)

variable {α : Type} (f : α → Nat → α)

partial def main (e : Expr) (offset : Nat) : M α Unit := do
  if offset < e.looseBVarRange then
    unless (← get).visited.contains (offset, e) do
      modify fun s => { s with visited := s.visited.insert (offset, e) }
      match e with
      | .bvar idx =>
        -- `idx ≥ offset` is true if `looseBVarRange` has not overflowed. It currently has the range [0,2^20).
        modify fun s => { s with value := f s.value (idx - offset) }
      | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => pure ()
      | .app f a => main f offset; main a offset
      | .lam _ t b _ | .forallE _ t b _ => main t offset; main b (offset + 1)
      | .letE _ t v b _ => main t offset; main v offset; main b (offset + 1)
      | .mdata _ e' => main e' offset
      | .proj _ _ e' => main e' offset

end FoldLooseBVars

/--
Folds `f` over all loose bvars appearing in `e`, once, with indices at least `offset`,
and the indices are given relative to `offset`.

Specification: With `B := { i | e.hasLooseBVar (i + offset) }` a set,
then `e.foldLooseBVars init f = B.fold init f`, with the fold performed in some unspecified order.
-/
def foldLooseBVars {α : Type} (e : Expr) (init : α) (f : α → Nat → α) (offset : Nat := 0) : α :=
  if e.hasLooseBVars then
    let (_, s) := FoldLooseBVars.main f e offset |>.run { value := init }
    s.value
  else
    init

/--
Collects the loose bound variables in `e` with indices at least `offset`.
Returns a set of indices relative to `offset`.

Specification: `i ∈ e.collectLooseBVars offset ↔ e.hasLooseBVar (i + offset)`.
-/
def collectLooseBVars (e : Expr) (offset : Nat := 0) : Std.HashSet Nat :=
  foldLooseBVars e {} Std.HashSet.insert offset

end Lean.Expr
