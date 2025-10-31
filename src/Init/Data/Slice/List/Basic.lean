/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Slice.Basic
public import Init.Data.Slice.Notation
public import Init.Data.Range.Polymorphic.Nat

set_option linter.missingDocs true

/-!
This module provides slice notation for list slices (a.k.a. `Sublist`) and implements an iterator
for those slices.
-/

open Std Std.Slice Std.PRange

/--
Internal representation of `ListSlice`, which is an abbreviation for `Slice ListSliceData`.
-/
public class Std.Slice.Internal.ListSliceData (α : Type u) where
  /-- The relevant suffix of the underlying list. -/
  list : List α
  /-- The maximum length of the slice, starting at the beginning of `list`. -/
  stop : Nat

/--
A region of some underlying list. List slices can be used to avoid copying or allocating space,
while being more convenient than tracking the bounds by hand.

A list slice only stores the suffix of the underlying list, starting from the range's lower bound
so that the cost of operations on the slice does not depend on the start position. However,
the cost of creating a list slice is linear in the start position.
-/
public abbrev ListSlice (α : Type u) := Slice (Internal.ListSliceData α)

variable {α : Type u}

/--
Returns a slice of a list with the given bounds.

If `start` or `stop` are not valid bounds for a subarray, then they are clamped to the list's length.
Additionally, the starting index is clamped to the ending index.

This function is linear in `start` because it stores `as.drop start` in the slice.
-/
public def List.toSlice (as : List α) (start : Nat) (stop : Nat) : ListSlice α :=
  if start ≤ stop then
    ⟨{ list := as.drop start, stop := stop - start }⟩
  else
    ⟨{ list := [], stop := 0 }⟩

public instance : Rcc.Sliceable (List α) Nat (ListSlice α) where
  mkSlice xs range :=
    let halfOpenRange := Rcc.HasRcoIntersection.intersection range 0...xs.length
    (xs.toSlice halfOpenRange.lower halfOpenRange.upper)

public instance : Rco.Sliceable (List α) Nat (ListSlice α) where
  mkSlice xs range :=
    let halfOpenRange := Rco.HasRcoIntersection.intersection range 0...xs.length
    (xs.toSlice halfOpenRange.lower halfOpenRange.upper)

public instance : Rci.Sliceable (List α) Nat (ListSlice α) where
  mkSlice xs range :=
    let halfOpenRange := Rci.HasRcoIntersection.intersection range 0...xs.length
    (xs.toSlice halfOpenRange.lower halfOpenRange.upper)

public instance : Roc.Sliceable (List α) Nat (ListSlice α) where
  mkSlice xs range :=
    let halfOpenRange := Roc.HasRcoIntersection.intersection range 0...xs.length
    (xs.toSlice halfOpenRange.lower halfOpenRange.upper)

public instance : Roo.Sliceable (List α) Nat (ListSlice α) where
  mkSlice xs range :=
    let halfOpenRange := Roo.HasRcoIntersection.intersection range 0...xs.length
    (xs.toSlice halfOpenRange.lower halfOpenRange.upper)

public instance : Roi.Sliceable (List α) Nat (ListSlice α) where
  mkSlice xs range :=
    let halfOpenRange := Roi.HasRcoIntersection.intersection range 0...xs.length
    (xs.toSlice halfOpenRange.lower halfOpenRange.upper)

public instance : Ric.Sliceable (List α) Nat (ListSlice α) where
  mkSlice xs range :=
    let halfOpenRange := Ric.HasRcoIntersection.intersection range 0...xs.length
    (xs.toSlice halfOpenRange.lower halfOpenRange.upper)

public instance : Rio.Sliceable (List α) Nat (ListSlice α) where
  mkSlice xs range :=
    let halfOpenRange := Rio.HasRcoIntersection.intersection range 0...xs.length
    (xs.toSlice halfOpenRange.lower halfOpenRange.upper)

public instance : Rii.Sliceable (List α) Nat (ListSlice α) where
  mkSlice xs _ :=
    let halfOpenRange := 0...<xs.length
    (xs.toSlice halfOpenRange.lower halfOpenRange.upper)
