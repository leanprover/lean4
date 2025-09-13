/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.PRange

public section

/-!
# Slice notation

This module provides the means to obtain a slice from a collection and a range of indices via
slice notation.
-/

open Std PRange

namespace Std.Slice

/--
This typeclass indicates how to obtain slices of elements of `α`.

Here, `β` is the type of ranges used to index the slices and `γ` is the type of the
slices. Usually, the range type `β` is one of `Rcc ι`, `Rco ι`, `Rci ι`, `Roc ι`, `Roo ι`, `Roi ι`,
`Ric ι`, `Rio ι` and `Rii ι`.
-/
class Sliceable (α : Type u) (β : outParam (Type v)) (γ : outParam (Type w)) where
  mkSlice (carrier : α) (range : β) : γ

macro_rules
  | `($c[*...*]) => `(Sliceable.mkSlice $c *...*)
  | `($c[$a...*]) => `(Sliceable.mkSlice $c $a...*)
  | `($c[$a<...*]) => `(Sliceable.mkSlice $c $a<...*)
  | `($c[*...<$b]) => `(Sliceable.mkSlice $c *...<$b)
  | `($c[$a...<$b]) => `(Sliceable.mkSlice $c $a...<$b)
  | `($c[$a<...<$b]) => `(Sliceable.mkSlice $c $a<...<$b)
  | `($c[*...$b]) => `(Sliceable.mkSlice $c *...<$b)
  | `($c[$a...$b]) => `(Sliceable.mkSlice $c $a...<$b)
  | `($c[$a<...$b]) => `(Sliceable.mkSlice $c $a<...<$b)
  | `($c[*...=$b]) => `(Sliceable.mkSlice $c *...=$b)
  | `($c[$a...=$b]) => `(Sliceable.mkSlice $c $a...=$b)
  | `($c[$a<...=$b]) => `(Sliceable.mkSlice $c $a<...=$b)

end Std.Slice
