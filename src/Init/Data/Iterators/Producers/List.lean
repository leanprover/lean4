/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Producers.Monadic.List

@[expose] public section

open Std Std.Iterators Std.Iterators.Types

/-!
# List iterator

This module provides an iterator for lists that is accessible via `List.iter`.
-/

/--
Returns a finite iterator for the given list.
The iterator yields the elements of the list in order and then terminates.

The monadic version of this iterator is `List.iterM`.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[always_inline, inline]
def List.iter {α : Type w} (l : List α) :
    Iter (α := ListIterator α) α :=
  ((l.iterM Id).toIter : Iter α)
