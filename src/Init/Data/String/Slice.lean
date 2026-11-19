/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving, Markus Himmel
-/
module

prelude
public import Init.Data.String.Slice.Basic
public import Init.Data.String.Slice.Pattern
public import Init.Data.String.Slice.Numeric

set_option doc.verso true

/-!
This module defines the programming API for {name}`String.Slice`. The API mostly consists of
functionality for searching for various kinds of pattern matches in slices to iterate over them,
provide subslices according to matches etc. The key design principles behind this module are:
- Instead of providing one function per kind of pattern the API is generic over various kinds of
  patterns. Thus it only provides e.g. one kind of function for looking for the position of the
  first occurrence of a pattern. Currently the supported patterns are:
  - {name}`Char`
  - {lean}`Char → Bool`
  - {name}`String` and {name}`String.Slice` (partially: doing non trivial searches backwards is not
    supported yet)
- Whenever a slice gets mutated a new slice is returned to allow for repeated chaining of functions
  with minimal allocations. If necessary the slice can ultimately be converted back to
  {name}`String` using {name}`String.Slice.copy`
- Instead of allocating intermediate collections the operations that iterate over slices in various
  ways (characters, positions etc.) return iterators that can be collected into other collections if
  necessary.
- When sensible the API provides functionality for searching both in a forward and backward manner
-/
