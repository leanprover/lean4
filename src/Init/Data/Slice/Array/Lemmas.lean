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

end Subarray

public theorem Array.toSubarray_eq_toSubarray_of_min_eq_min {xs : Array α}
    {start stop stop' : Nat} (h : min stop xs.size = min stop' xs.size) :
    xs.toSubarray start stop = xs.toSubarray start stop' := by
  simp only [Array.toSubarray]
  split
  · split
    · have h₁ : start ≤ xs.size := by omega
      have h₂ : start ≤ stop' := by omega
      simp only [dif_pos h₁, dif_pos h₂]
      split
      · simp_all
      · simp_all [Nat.min_eq_right (Nat.le_of_lt _)]
    · simp only [Nat.min_eq_left, *] at h
      split
      · simp only [Nat.min_eq_left, *] at h
        simp [h]
        omega
      · simp [Nat.min_eq_right (Nat.le_of_not_ge _), *] at h
        simp [h]
        omega
  · split
    · split
      · simp [Nat.min_eq_right (Nat.le_of_not_ge _), *] at h
        simp_all
        omega
      · simp
    · simp [Nat.min_eq_right (Nat.le_of_not_ge _), *] at h
      split
      · simp [*] at h
        simp_all
        omega
      · simp

@[simp]
public theorem Array.array_rccSlice {xs : Array α} {lo hi : Nat} :
    xs[lo...=hi].array = xs := by
  simp [Std.Rcc.Sliceable.mkSlice, Array.toSubarray, apply_dite]
  simp [Subarray.array]

namespace Subarray

theorem toList_eq {xs : Subarray α} :
    xs.toList = (xs.array.extract xs.start xs.stop).toList := by
  simp only [Std.Slice.toList]
  rw [Iter.toList_eq_match_step]

public theorem rccSlice_eq {xs : Subarray α} {lo hi : Nat} :
    xs[lo...=hi] = xs.array[(xs.start + lo)...(xs.start + min (hi + 1) xs.size)] := by
  simp [Std.Rcc.Sliceable.mkSlice, Std.Rcc.HasRcoIntersection.intersection,
    Std.Rco.Sliceable.mkSlice, Std.Rco.HasRcoIntersection.intersection,
    Nat.add_comm lo]
  apply Array.toSubarray_eq_toSubarray_of_min_eq_min
  omega

-- this is false!
public theorem rccSlice_rccSlice_array {xs : Array α} :
    xs[lo...=hi][lo'...=hi'] = xs[(lo + lo')...(lo + min (hi' + 1) (hi + 1 - lo))] := by
  simp [rccSlice_eq]
  simp [Std.Rcc.Sliceable.mkSlice]
  simp [Std.Rcc.HasRcoIntersection.intersection]
  simp [Array.toSubarray, Nat.min_le_right, Subarray.start, Subarray.stop, Subarray.size]
  split
  · simp
  · simp

end Subarray
