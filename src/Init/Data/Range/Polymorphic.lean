/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.Basic
public import Init.Data.Range.Polymorphic.Iterators
public import Init.Data.Range.Polymorphic.Lemmas
public import Init.Data.Range.Polymorphic.Nat
public import Init.Data.Range.Polymorphic.NatLemmas

public section

/-!
# Polymorphic ranges

Any type that provides certain typeclasses supports range notation: For example, `2...<5`
stands for the numbers at least `2` and smaller than `5`. Such ranges support iteration with
`for .. in` and can be converted into a list with `PRange.toList`. After importing
`Std.Data.Iterators`, there will also be `PRange.iter`, which provides an iterator over the
elements of the range.

In order to support ranges of a certain type `α`, multiple instances need to be implemented.
An example of how this plays out can be found in `Init.Data.Range.Polymorphic.Nat`.

The typeclass system is experimental and will change soon, so at this point it is not recommended
to provide custom ranges outside of the standard library.
-/
