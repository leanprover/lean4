/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Slice.Basic
public import Init.Data.Slice.Notation

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
  stop : Option Nat

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

If `start` or `stop` are not valid bounds for a sublist, then they are clamped to the list's length.
Additionally, the starting index is clamped to the ending index.

This function is linear in `start` because it stores `as.drop start` in the slice.
-/
public def List.toSlice (as : List α) (start : Nat) (stop : Nat) : ListSlice α :=
  if start < stop then
    ⟨{ list := as.drop start, stop := some (stop - start) }⟩
  else
    ⟨{ list := [], stop := some 0 }⟩

/--
Returns a slice of a list with the given lower bound.

If `start` is not a valid bound for a sublist, then they are clamped to the list's length.

This function is linear in `start` because it stores `as.drop start` in the slice.
-/
public def List.toUnboundedSlice (as : List α) (start : Nat) : ListSlice α :=
  ⟨{ list := as.drop start, stop := none }⟩

public instance : Rcc.Sliceable (List α) Nat (ListSlice α) where
  mkSlice xs range :=
    xs.toSlice range.lower (range.upper + 1)

public instance : Rco.Sliceable (List α) Nat (ListSlice α) where
  mkSlice xs range :=
    xs.toSlice range.lower range.upper

public instance : Rci.Sliceable (List α) Nat (ListSlice α) where
  mkSlice xs range :=
    xs.toUnboundedSlice range.lower

public instance : Roc.Sliceable (List α) Nat (ListSlice α) where
  mkSlice xs range :=
    xs.toSlice (range.lower + 1) (range.upper + 1)

public instance : Roo.Sliceable (List α) Nat (ListSlice α) where
  mkSlice xs range :=
    xs.toSlice (range.lower + 1) range.upper

public instance : Roi.Sliceable (List α) Nat (ListSlice α) where
  mkSlice xs range :=
    xs.toUnboundedSlice (range.lower + 1)

public instance : Ric.Sliceable (List α) Nat (ListSlice α) where
  mkSlice xs range :=
    xs.toSlice 0 (range.upper + 1)

public instance : Rio.Sliceable (List α) Nat (ListSlice α) where
  mkSlice xs range :=
    xs.toSlice 0 range.upper

public instance : Rii.Sliceable (List α) Nat (ListSlice α) where
  mkSlice xs _ :=
    xs.toUnboundedSlice 0

public instance : Rcc.Sliceable (ListSlice α) Nat (ListSlice α) where
  mkSlice xs range :=
    let stop := match xs.internalRepresentation.stop with
      | none => range.upper + 1
      | some stop => min stop (range.upper + 1)
    xs.internalRepresentation.list[range.lower...stop]

public instance : Rco.Sliceable (ListSlice α) Nat (ListSlice α) where
  mkSlice xs range :=
    let stop := match xs.internalRepresentation.stop with
      | none => range.upper
      | some stop => min stop range.upper
    xs.internalRepresentation.list[range.lower...stop]

public instance : Rci.Sliceable (ListSlice α) Nat (ListSlice α) where
  mkSlice xs range :=
    match xs.internalRepresentation.stop with
    | none => xs.internalRepresentation.list[range.lower...*]
    | some stop => xs.internalRepresentation.list[range.lower...stop]

public instance : Roc.Sliceable (ListSlice α) Nat (ListSlice α) where
  mkSlice xs range :=
    let stop := match xs.internalRepresentation.stop with
      | none => range.upper + 1
      | some stop => min stop (range.upper + 1)
    xs.internalRepresentation.list[range.lower<...stop]

public instance : Roo.Sliceable (ListSlice α) Nat (ListSlice α) where
  mkSlice xs range :=
    let stop := match xs.internalRepresentation.stop with
      | none => range.upper
      | some stop => min stop range.upper
    xs.internalRepresentation.list[range.lower<...stop]

public instance : Roi.Sliceable (ListSlice α) Nat (ListSlice α) where
  mkSlice xs range :=
    match xs.internalRepresentation.stop with
    | none => xs.internalRepresentation.list[range.lower<...*]
    | some stop => xs.internalRepresentation.list[range.lower<...stop]

public instance : Ric.Sliceable (ListSlice α) Nat (ListSlice α) where
  mkSlice xs range :=
    let stop := match xs.internalRepresentation.stop with
      | none => range.upper + 1
      | some stop => min stop (range.upper + 1)
    xs.internalRepresentation.list[*...stop]

public instance : Rio.Sliceable (ListSlice α) Nat (ListSlice α) where
  mkSlice xs range :=
    let stop := match xs.internalRepresentation.stop with
      | none => range.upper
      | some stop => min stop range.upper
    xs.internalRepresentation.list[*...stop]

public instance : Rii.Sliceable (ListSlice α) Nat (ListSlice α) where
  mkSlice xs _ :=
    xs
