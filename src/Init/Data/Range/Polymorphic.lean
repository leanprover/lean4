/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Range.Polymorphic.Basic
import Init.Data.Range.Polymorphic.Lemmas
import Init.Data.Range.Polymorphic.Nat

/-!
# Polymorphic ranges

Any type that provides certain typeclasses supports range notation: For example, `[2..<5]`
stands for the numbers at least `2` and smaller than `5`. Such ranges support iteration with
`for .. in` and can be converted into a list with `PRange.toList`. After importing
`Std.Data.Iterators`, there will also be `PRange.iter`, which provides an iterator over the
elements of the range.

In order to support ranges of a certain type `α`, the following instances need to be implemented:

* `LE α` and `DecidableLE α` for inclusive upper and lower bounds
* `LT α` and `DecidableLT α` for exclusive upper and lower bounds
* `UpwardEnumerable α` for iteration over the ranges
* `LawfulUpwardEnumerableUpperBound upperBoundShape α` and
  `LawfulUpwardEnumerableLowerBound lowerBoundShape α` for iteration
* `HasFiniteRanges upperBoundShape α` for termination of iteration
* `Least? α` for iteration over lower-unbounded ranges

An example for how this plays out can be found in `Init.Data.Range.Polymorphic.Nat`.
-/
