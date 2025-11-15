/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import all Init.Data.Array.Subarray
import all Init.Data.Slice.Array.Basic
import Init.Data.Slice.Lemmas
public import Init.Data.Slice.Array.Iterator
import all Init.Data.Slice.Array.Iterator
import all Init.Data.Slice.Operations
import all Init.Data.Range.Polymorphic.Iterators
public import Init.Data.Range.Polymorphic.Lemmas
import all Init.Data.Range.Polymorphic.Lemmas
public import Init.Data.Slice.Lemmas
public import Init.Data.Iterators.Lemmas

open Std Std.Iterators Std.PRange Std.Slice

namespace Subarray

theorem internalIter_eq {α : Type u} {s : Subarray α} :
    Internal.iter s = (Rco.Internal.iter (s.start...<s.stop)
      |>.attachWith (· < s.array.size)
        (fun out h => h
            |> Rco.Internal.isPlausibleIndirectOutput_iter_iff.mp
            |> Rco.lt_upper_of_mem
            |> (Nat.lt_of_lt_of_le · s.stop_le_array_size))
      |>.uLift
      |>.map fun | .up i => s.array[i.1]) := by
  simp [Internal.iter, ToIterator.iter_eq, Subarray.start, Subarray.stop, Subarray.array]

theorem toList_internalIter {α : Type u} {s : Subarray α} :
    (Internal.iter s).toList =
      ((s.start...s.stop).toList
        |>.attach
        |>.map fun i => s.array[i.1]'(i.property
            |> Rco.mem_toList_iff_mem.mp
            |> Rco.lt_upper_of_mem
            |> (Nat.lt_of_lt_of_le · s.stop_le_array_size))) := by
  rw [internalIter_eq, Iter.toList_map, Iter.toList_uLift, Iter.toList_attachWith]
  simp [Rco.toList]

public instance : LawfulSliceSize (Internal.SubarrayData α) where
  lawful s := by
    simp [SliceSize.size, ToIterator.iter_eq, Iter.toIter_toIterM,
      ← Iter.size_toArray_eq_count, ← Rco.Internal.toArray_eq_toArray_iter,
      Rco.size_toArray, Rco.size, Rxo.HasSize.size, Rxc.HasSize.size]
    omega

public theorem toArray_eq_sliceToArray {α : Type u} {s : Subarray α} :
    s.toArray = Slice.toArray s := by
  simp [Subarray.toArray, Array.ofSubarray]

@[simp]
public theorem forIn_toList {α : Type u} {s : Subarray α}
    {m : Type v → Type w} [Monad m] [LawfulMonad m] {γ : Type v} {init : γ}
    {f : α → γ → m (ForInStep γ)} :
    ForIn.forIn s.toList init f = ForIn.forIn s init f :=
  Slice.forIn_toList

@[simp]
public theorem forIn_toArray {α : Type u} {s : Subarray α}
    {m : Type v → Type w} [Monad m] [LawfulMonad m] {γ : Type v} {init : γ}
    {f : α → γ → m (ForInStep γ)} :
    ForIn.forIn s.toArray init f = ForIn.forIn s init f :=
  Slice.forIn_toArray

public theorem rccSlice_eq {xs : Subarray α} {lo hi : Nat} :
    xs[lo...=hi] = xs.array[(xs.start + lo)...=(xs.start + min (hi + 1) xs.size)] := by
  simp [Std.Rcc.Sliceable.mkSlice, Std.Rcc.HasRcoIntersection.intersection,
    ]

public theorem rccSlice_rccSlice_array {xs : Array α} :

end Subarray
