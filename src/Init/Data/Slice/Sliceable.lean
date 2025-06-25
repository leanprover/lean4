/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Range.Polymorphic.PRange

open Std PRange

namespace Std.Slice

/--
This typeclass signifies that the type `α` supports slice notation with index type `β`.
The slices contain elements of type `γ`.
-/
class Sliceable (shape : RangeShape) (α : Type u) (β : outParam (Type v))
    (γ : outParam (Type w)) where
  mkSlice (carrier : α) (range : PRange shape β) : γ


end Std.Slice
