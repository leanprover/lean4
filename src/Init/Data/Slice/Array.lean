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

open Std.Slice Std.PRange

instance {shape} {α : Type u} : Sliceable shape (Array α) Nat α where

instance [ClosedOpenIntersection shape Nat] [SupportsLowerBound shape.lower Nat]
    [SupportsUpperBound shape.upper Nat] [LawfulClosedOpenIntersection shape Nat] :
    SliceIter shape (Array α) :=
  .of _ fun s =>
    Internal.iter (ClosedOpenIntersection.intersection s.range (Std.PRange.mk 0 s.carrier.size))
      |>.attachWith (· < s.carrier.size) (by
        simp only [Internal.isPlausibleIndirectOutput_iter_iff,
          LawfulClosedOpenIntersection.mem_intersection_iff]
        simp [Membership.mem, SupportsUpperBound.IsSatisfied])
      |>.map fun i => s.carrier[i.1]
