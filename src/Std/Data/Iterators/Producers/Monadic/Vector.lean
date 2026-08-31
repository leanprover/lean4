/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Vector.Basic
public import Std.Data.Iterators.Producers.Monadic.Array

set_option doc.verso true

/-!
# Vector iterator

This module provides an iterator for vectors that is accessible via
{name (scope := "Std.Data.Iterators.Producers.Monadic.Vector")}`Vector.iterM`.
-/

@[expose] public section

open Std Std.Iterators

/--
Returns a finite monadic iterator for the given vector starting at the given index.
The iterator yields the elements of the vector in order and then terminates.

The pure version of this iterator is
{name (scope := "Std.Data.Iterators.Producers.Vector")}`Vector.iterFromIdx`.

**Termination properties:**

* {name}`Finite` instance: always
* {name}`Productive` instance: always
-/
@[always_inline, inline, match_pattern]
def _root_.Vector.iterFromIdxM (xs : Vector α n) (m : Type w → Type w')
    (pos : Nat) [Pure m] :=
  (xs.toArray.iterFromIdxM m pos : IterM m α)

/--
Returns a finite monadic iterator for the given vector.
The iterator yields the elements of the vector in order and then terminates. There are no side
effects.

The pure version of this iterator is
{name (scope := "Std.Data.Iterators.Producers.Vector")}`Vector.iter`.

**Termination properties:**

* {name}`Finite` instance: always
* {name}`Productive` instance: always
-/
@[inline]
def Vector.iterM (xs : Vector α n) (m : _) [Pure m] :=
  (xs.toArray.iterM m : IterM m α)
