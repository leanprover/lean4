/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.Basic
public import Init.Data.Vector.Basic

public section

/-!
This module contains an advanced `GetElem` tactic extension for polymorphic ranges.
While `Init.Data.Range.Polymorphic.Basic` already defines one, it only works in very
basic cases where the open upper bound of the range is exactly the size of the collection.

This tactic is using `omega` to be more powerful, but it needs special handling for `Vector`,
which is impossible in `Init.Data.Range.Polymorphic.Basic` for bootstrapping reasons.
-/

macro_rules
  | `(tactic| get_elem_tactic_extensible) =>
    `(tactic|
      first
        | rw [Std.PRange.mem_iff_isSatisfied] at *
          dsimp +zetaDelta only [Std.PRange.SupportsLowerBound.IsSatisfied, Std.PRange.SupportsUpperBound.IsSatisfied,
            -- `Vector.size` needs to be unfolded because for `xs : Vector α n`, one needs to prove
            -- `i < n` instead of `i < xs.size`. Although `Vector.size` is reducible, this is
            -- not enough for `omega`.
            Vector.size] at *
          omega
        | done)
