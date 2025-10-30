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

/-!
This module provides slice notation for list slices (a.k.a. `Sublist`) and implements an iterator
for those slices.
-/

open Std Std.Slice Std.PRange

public class Std.Slice.Internal.ListSliceData (α : Type u) where
  list : List α
  stop : Nat

public abbrev ListSlice (α : Type u) := Slice (Internal.ListSliceData α)

variable {α : Type u}

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
