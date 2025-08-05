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

variable {shape : RangeShape} {α : Type u}

instance [ClosedOpenIntersection shape Nat] :
    Sliceable shape (Array α) Nat (Subarray α) where
  mkSlice xs range :=
    let halfOpenRange := ClosedOpenIntersection.intersection range 0...<xs.size
    (xs.toSubarray halfOpenRange.lower halfOpenRange.upper)
