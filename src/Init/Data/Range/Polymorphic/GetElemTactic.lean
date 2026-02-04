/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Vector.Basic
public import Init.Data.Slice.Array.Lemmas

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
        | try rw [Std.Rcc.mem_iff] at *
          try rw [Std.Rco.mem_iff] at *
          try rw [Std.Rci.mem_iff] at *
          try rw [Std.Roc.mem_iff] at *
          try rw [Std.Roo.mem_iff] at *
          try rw [Std.Roi.mem_iff] at *
          try rw [Std.Ric.mem_iff] at *
          try rw [Std.Rio.mem_iff] at *
          try rw [Std.Rii.mem_iff] at *
          try dsimp +zetaDelta only [
            -- `Vector.size` needs to be unfolded because for `xs : Vector α n`, one needs to prove
            -- `i < n` instead of `i < xs.size`. Although `Vector.size` is reducible, this is
            -- not enough for `omega`.
            Vector.size] at *
          -- If we're accessing elements of a subarray, we need to calculate its size.
          try simp only [
            Array.size_mkSlice_rco, Array.size_mkSlice_rcc, Array.size_mkSlice_rci,
            Array.size_mkSlice_roo, Array.size_mkSlice_roc, Array.size_mkSlice_roi,
            Array.size_mkSlice_rio, Array.size_mkSlice_ric, Array.size_mkSlice_rii]
          omega
        | done)
