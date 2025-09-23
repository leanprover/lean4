/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Core
public import Init.Data.Array.Subarray
public import Init.Data.Slice.Notation
public import Init.Data.Range.Polymorphic.Nat

public section

/-!
This module provides slice notation for array slices (a.k.a. `Subarray`) and implements an iterator
for those slices.
-/

open Std Slice PRange

variable {α : Type u}

instance : Rcc.Sliceable (Array α) Nat (Subarray α) where
  mkSlice xs range :=
    let halfOpenRange := Rcc.HasRcoIntersection.intersection range 0...<xs.size
    (xs.toSubarray halfOpenRange.lower halfOpenRange.upper)

instance : Rco.Sliceable (Array α) Nat (Subarray α) where
  mkSlice xs range :=
    let halfOpenRange := Rco.HasRcoIntersection.intersection range 0...<xs.size
    (xs.toSubarray halfOpenRange.lower halfOpenRange.upper)

instance : Rci.Sliceable (Array α) Nat (Subarray α) where
  mkSlice xs range :=
    let halfOpenRange := Rci.HasRcoIntersection.intersection range 0...<xs.size
    (xs.toSubarray halfOpenRange.lower halfOpenRange.upper)

instance : Roc.Sliceable (Array α) Nat (Subarray α) where
  mkSlice xs range :=
    let halfOpenRange := Roc.HasRcoIntersection.intersection range 0...<xs.size
    (xs.toSubarray halfOpenRange.lower halfOpenRange.upper)

instance : Roo.Sliceable (Array α) Nat (Subarray α) where
  mkSlice xs range :=
    let halfOpenRange := Roo.HasRcoIntersection.intersection range 0...<xs.size
    (xs.toSubarray halfOpenRange.lower halfOpenRange.upper)

instance : Roi.Sliceable (Array α) Nat (Subarray α) where
  mkSlice xs range :=
    let halfOpenRange := Roi.HasRcoIntersection.intersection range 0...<xs.size
    (xs.toSubarray halfOpenRange.lower halfOpenRange.upper)

instance : Ric.Sliceable (Array α) Nat (Subarray α) where
  mkSlice xs range :=
    let halfOpenRange := Ric.HasRcoIntersection.intersection range 0...<xs.size
    (xs.toSubarray halfOpenRange.lower halfOpenRange.upper)

instance : Rio.Sliceable (Array α) Nat (Subarray α) where
  mkSlice xs range :=
    let halfOpenRange := Rio.HasRcoIntersection.intersection range 0...<xs.size
    (xs.toSubarray halfOpenRange.lower halfOpenRange.upper)

instance : Rii.Sliceable (Array α) Nat (Subarray α) where
  mkSlice xs _ :=
    let halfOpenRange := 0...<xs.size
    (xs.toSubarray halfOpenRange.lower halfOpenRange.upper)
