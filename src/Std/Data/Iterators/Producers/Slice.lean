/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Slice.Operations

@[expose] public section

/-!
# Slice iterator

This module provides iterators over slices from `Std.Slice` via `Std.Slice.iter`.
-/

/--
Returns an iterator over the given slice. This iterator will emit the elements of the slice
in increasing order of the indices.
-/
@[always_inline, inline]
def Std.Slice.iter [ToIterator (Slice γ) Id α β] (s : Slice γ) :=
  (Internal.iter s : Iter β)
