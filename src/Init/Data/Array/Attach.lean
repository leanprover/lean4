/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner, Mario Carneiro
-/
prelude
import Init.Data.Array.Mem
import Init.Data.List.Attach

namespace Array

/--
Unsafe implementation of `attachWith`, taking advantage of the fact that the representation of
`Array {x // P x}` is the same as the input `Array α`.
-/
@[inline] private unsafe def attachWithImpl
    (xs : Array α) (P : α → Prop) (_ : ∀ x ∈ xs, P x) : Array {x // P x} := unsafeCast xs

/-- `O(1)`. "Attach" a proof `P x` that holds for all the elements of `xs` to produce a new array
  with the same elements but in the type `{x // P x}`. -/
@[implemented_by attachWithImpl] def attachWith
    (xs : Array α) (P : α → Prop) (H : ∀ x ∈ xs, P x) : Array {x // P x} :=
  ⟨xs.toList.attachWith P fun x h => H x (Array.Mem.mk h)⟩

/-- `O(1)`. "Attach" the proof that the elements of `xs` are in `xs` to produce a new array
  with the same elements but in the type `{x // x ∈ xs}`. -/
@[inline] def attach (xs : Array α) : Array {x // x ∈ xs} := xs.attachWith _ fun _ => id

end Array
