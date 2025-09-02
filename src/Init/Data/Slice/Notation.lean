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
This typeclass indicates how to obtain slices of `α` of type `γ`, given ranges of shape `shape` in
the index type `β`.
-/
class Sliceable (shape : RangeShape) (α : Type u) (β : outParam (Type v))
    (γ : outParam (Type w)) where
  mkSlice (carrier : α) (range : PRange shape β) : γ

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
