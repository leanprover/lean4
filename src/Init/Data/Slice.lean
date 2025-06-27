/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Slice.Basic
import Init.Data.Slice.Notation
import Init.Data.Slice.Operations
import Init.Data.Slice.Array

public section

/-!
# Polymorphic slices

This module provides slices -- views on a subset of all elements of an array or other collection,
demarcated by a range of indices.

* `Init.Data.Slice.Basic` defines the `Slice` structure. All slices are of this type.
* `Init.Data.Slice.Operations` provides functions on `Slice` via dot notation. Many of them are
  implemented using iterators under the hood.
* `Init.Data.Slice.Notation` provides slice notation based on ranges, relying on the `Sliceable`
  typeclass.
* `Init.Data.Slice.Array` provides the `Sliceable` instance for array slices.
-/
