/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Vector.Basic
public import Std.Data.Iterators.Producers.Array

set_option doc.verso true

/-!
# Vector iterator

This module provides an iterator for vectors that is accessible via
{name (scope := "Std.Data.Iterators.Producers.Vector")}`Vector.iter`.
-/

@[expose] public section

open Std Std.Iterators

/--
Returns a finite iterator for the given vector starting at the given index.
The iterator yields the elements of the vector in order and then terminates.

The monadic version of this iterator is
{name (scope := "Std.Data.Iterators.Producers.Monadic.Vector")}`Vector.iterFromIdxM`.

**Termination properties:**

* {name}`Finite` instance: always
* {name}`Productive` instance: always
-/
@[always_inline, inline]
def Vector.iterFromIdx {α : Type w} (xs : Vector α n) (pos : Nat) :=
  (xs.toArray.iterFromIdx pos : Iter α)

/--
Returns a finite iterator for the given vector.
The iterator yields the elements of the vector in order and then terminates.

The monadic version of this iterator is
{name (scope := "Std.Data.Iterators.Producers.Monadic.Vector")}`Vector.iterM`.

**Termination properties:**

* {name}`Finite` instance: always
* {name}`Productive` instance: always
-/
@[always_inline, inline]
def Vector.iter {α : Type w} (xs : Vector α n) :=
  (xs.toArray.iter : Iter α)
