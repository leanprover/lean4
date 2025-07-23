/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.Iterators

@[expose] public section

/-!
# Range iterator

This module provides iterators over ranges from `Std.PRange` via `Std.PRange.iter`.
-/

open Std.PRange

/--
Returns an iterator over the given range. This iterator will emit the elements of the range
in increasing order.
-/
@[always_inline, inline]
def Std.PRange.iter [UpwardEnumerable α] [BoundedUpwardEnumerable sl α]
    (r : PRange ⟨sl, su⟩ α) : Iter (α := RangeIterator su α) α :=
  ⟨⟨BoundedUpwardEnumerable.init? r.lower, r.upper⟩⟩
