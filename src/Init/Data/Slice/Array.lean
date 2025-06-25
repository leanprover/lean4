/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Core
import Init.Data.Range.Polymorphic.Basic
import Init.Data.Range.Polymorphic.Nat
import all Init.Data.Range.Polymorphic.Basic
import Init.Data.Slice.Basic
import Init.Data.Iterators.Combinators.Attach
import Init.Data.Iterators.Combinators.FilterMap
import Init.Data.Array.Subarray

open Std Slice PRange

abbrev Std.Slice.Subarray' (α : Type u) := Slice (Subarray α)

instance {α : Type u} : Self (Slice (Subarray α)) (Subarray' α) where

instance {shape} {α : Type u} [ClosedOpenIntersection shape Nat] :
    Sliceable shape (Array α) Nat (Subarray' α) where
  mkSlice xs range :=
    let halfOpenRange := ClosedOpenIntersection.intersection range (0)...<xs.size
    ⟨xs.toSubarray halfOpenRange.lower halfOpenRange.upper⟩

instance {s : Subarray' α} : ToIterator s Id α :=
  .of _
    (PRange.Internal.iter (s.internalRepresentation.start...<s.internalRepresentation.stop)
      |>.attachWith (· < s.internalRepresentation.array.size) (by
        simp only [Internal.isPlausibleIndirectOutput_iter_iff, Membership.mem,
          SupportsUpperBound.IsSatisfied, and_imp]
        intro out _ h
        have := s.internalRepresentation.stop_le_array_size
        omega)
      |>.map fun i => s.internalRepresentation.array[i.1])
