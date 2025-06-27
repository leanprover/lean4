/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Producers.Monadic.Array

/-!
# Array iterator

This module provides an iterator for arrays that is accessible via `Array.iter`.
-/

namespace Std.Iterators

/--
Returns a finite iterator for the given array starting at the given index.
The iterator yields the elements of the array in order and then terminates.

The monadic version of this iterator is `Array.iterFromIdxM`.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[always_inline, inline]
def _root_.Array.iterFromIdx {α : Type w} (l : Array α) (pos : Nat) :
    Iter (α := ArrayIterator α) α :=
  ((l.iterFromIdxM Id pos).toIter : Iter α)

/--
Returns a finite iterator for the given array.
The iterator yields the elements of the array in order and then terminates.

The monadic version of this iterator is `Array.iterM`.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[always_inline, inline]
def _root_.Array.iter {α : Type w} (l : Array α) :
    Iter (α := ArrayIterator α) α :=
  ((l.iterM Id).toIter : Iter α)

end Std.Iterators
