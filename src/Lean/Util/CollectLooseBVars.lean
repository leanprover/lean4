/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
prelude
import Lean.Expr

/-!
# Collecting set of loose bound variables

This module provides a function for collecting the set of loose bvars in an expression.
This means finding the set of `i` for which `e.hasLooseBVar i` is true.
-/

namespace Lean.Expr

namespace CollectLooseBVars

structure State where
  visited : Std.HashSet (Nat × Expr) := {}
  bvars : Std.HashSet Nat := {}

abbrev M := StateM State

partial def main (e : Expr) (offset : Nat) : M Unit := do
  if offset < e.looseBVarRange then
    unless (← get).visited.contains (offset, e) do
      modify fun s => { s with visited := s.visited.insert (offset, e) }
      match e with
      | .bvar idx =>
        -- `idx ≥ offset` is true if `looseBVarRange` has not overflowed. It currently has the range [0,2^20).
        modify fun s => { s with bvars := s.bvars.insert (idx - offset) }
      | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => pure ()
      | .app f a => main f offset; main a offset
      | .lam _ t b _ | .forallE _ t b _ => main t offset; main b (offset + 1)
      | .letE _ t v b _ => main t offset; main v offset; main b (offset + 1)
      | .mdata _ e' => main e' offset
      | .proj _ _ e' => main e' offset

end CollectLooseBVars

/--
Collects the loose bound variables in `e` with indices at least `offset`.
Returns a set of indices relative to `offset`.

Specification: `i ∈ e.collectLooseBVars offset ↔ e.hasLooseBVar (i + offset)`.
-/
def collectLooseBVars (e : Expr) (offset : Nat := 0) : Std.HashSet Nat :=
  if e.hasLooseBVars then
    let (_, s) := CollectLooseBVars.main e offset |>.run {}
    s.bvars
  else
    {}

end Lean.Expr
