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
import Init.Data.Slice.List.Lemmas
import Init.Data.Range.Polymorphic.NatLemmas

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
  simp [Std.Rcc.Sliceable.mkSlice, Array.toSubarray, apply_dite, Subarray.array]

public theorem Array.toSubarray_eq_min {xs : Array α} {lo hi : Nat} :
    xs.toSubarray lo hi = ⟨⟨xs, min lo (min hi xs.size), min hi xs.size, Nat.min_le_right _ _,
      Nat.min_le_right _ _⟩⟩ := by
  simp only [Array.toSubarray]
  split <;> split <;> simp [Nat.min_eq_right (Nat.le_of_not_ge _), *]

@[simp]
public theorem Array.array_toSubarray {xs : Array α} {lo hi : Nat} :
    (xs.toSubarray lo hi).array = xs := by
  simp [toSubarray_eq_min, Subarray.array]

@[simp]
public theorem Array.start_toSubarray {xs : Array α} {lo hi : Nat} :
    (xs.toSubarray lo hi).start = min lo (min hi xs.size) := by
  simp [toSubarray_eq_min, Subarray.start]

@[simp]
public theorem Array.stop_toSubarray {xs : Array α} {lo hi : Nat} :
    (xs.toSubarray lo hi).stop = min hi xs.size := by
  simp [toSubarray_eq_min, Subarray.stop]

theorem Subarray.toList_eq {xs : Subarray α} :
    xs.toList = (xs.array.extract xs.start xs.stop).toList := by
  let aslice := xs
  obtain ⟨⟨array, start, stop, h₁, h₂⟩⟩ := xs
  let lslice : ListSlice α := ⟨array.toList.drop start, some (stop - start)⟩
  simp only [Subarray.start, Subarray.stop, Subarray.array]
  change aslice.toList = _
  have : aslice.toList = lslice.toList := by
    simp [ListSlice.toList_eq, lslice, aslice]
    simp only [Std.Slice.toList, Std.Slice.Array.toList_internalIter]
    apply List.ext_getElem
    · have : stop - start ≤ array.size - start := by omega
      simp [Subarray.start, Subarray.stop, Std.PRange.Nat.size_rco, *]
    · intros
      simp [Subarray.array, Subarray.start, Subarray.stop, Std.Rco.getElem_toList_eq, succMany?]
  simp [this, ListSlice.toList_eq, lslice]

namespace Array

public theorem mkSlice_rco_eq_mkSlice_rco_min {xs : Array α} {lo hi : Nat} :
    xs[lo...hi] = xs[(min lo (min hi xs.size))...(min hi xs.size)] := by
  simp [Std.Rco.Sliceable.mkSlice, Array.toSubarray_eq_min, Std.Rco.HasRcoIntersection.intersection,
    Std.Rco.HasRcoIntersection.intersection]

@[simp]
public theorem toList_mkSlice_rco {xs : Array α} {lo hi : Nat} :
    xs[lo...hi].toList = (xs.toList.take hi).drop lo := by
  rw [List.take_eq_take_min, List.drop_eq_drop_min]
  simp [Std.Rco.Sliceable.mkSlice, Subarray.toList_eq, Std.Rco.HasRcoIntersection.intersection, List.take_drop,
    Nat.add_sub_of_le (Nat.min_le_right _ _)]

@[simp]
public theorem mkSlice_rcc_eq_mkSlice_rco {xs : Array α} {lo hi : Nat} :
    xs[lo...=hi] = xs[lo...(hi + 1)] := by
  simp [Std.Rcc.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice, Std.Rcc.HasRcoIntersection.intersection, Std.Rco.HasRcoIntersection.intersection]

public theorem mkSlice_rcc_eq_mkSlice_rco_min {xs : Array α} {lo hi : Nat} :
    xs[lo...=hi] = xs[(min lo (min (hi + 1) xs.size))...(min (hi + 1) xs.size)] := by
  simp [mkSlice_rco_eq_mkSlice_rco_min]

@[simp]
public theorem toList_mkSlice_rcc {xs : Array α} {lo hi : Nat} :
    xs[lo...=hi].toList = (xs.toList.take (hi + 1)).drop lo := by
  rw [mkSlice_rcc_eq_mkSlice_rco, toList_mkSlice_rco]

@[simp]
public theorem mkSlice_rci_eq_mkSlice_rco {xs : Array α} {lo : Nat} :
    xs[lo...*] = xs[lo...xs.size] := by
  simp [Std.Rci.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice, Std.Rci.HasRcoIntersection.intersection, Std.Rco.HasRcoIntersection.intersection]

public theorem mkSlice_rci_eq_mkSlice_rco_min {xs : Array α} {lo : Nat} :
    xs[lo...*] = xs[(min lo xs.size)...xs.size] := by
  simp [mkSlice_rco_eq_mkSlice_rco_min]

@[simp]
public theorem toList_mkSlice_rci {xs : Array α} {lo : Nat} :
    xs[lo...*].toList = xs.toList.drop lo := by
  rw [mkSlice_rci_eq_mkSlice_rco, toList_mkSlice_rco, ← Array.length_toList, List.take_length]
  -- TODO: nonconfluence of `Array.length_toList` and `List.take_length`

@[simp]
public theorem mkSlice_roo_eq_mkSlice_rco {xs : Array α} {lo hi : Nat} :
    xs[lo<...hi] = xs[(lo + 1)...hi] := by
  simp [Std.Roo.Sliceable.mkSlice, Std.Roo.HasRcoIntersection.intersection,
    Std.Rco.Sliceable.mkSlice, Std.Rco.HasRcoIntersection.intersection]

public theorem mkSlice_roo_eq_mkSlice_roo_min {xs : Array α} {lo hi : Nat} :
    xs[lo<...hi] = xs[(min (lo + 1) (min hi xs.size))...(min hi xs.size)] := by
  simp [mkSlice_rco_eq_mkSlice_rco_min]

@[simp]
public theorem toList_mkSlice_roo {xs : Array α} {lo hi : Nat} :
    xs[lo<...hi].toList = (xs.toList.take hi).drop (lo + 1) := by
  rw [mkSlice_roo_eq_mkSlice_rco, toList_mkSlice_rco]

@[simp]
public theorem mkSlice_roc_eq_mkSlice_roo {xs : Array α} {lo hi : Nat} :
    xs[lo<...=hi] = xs[lo<...(hi + 1)] := by
  simp [Std.Roc.Sliceable.mkSlice, Std.Roo.Sliceable.mkSlice, Std.Roc.HasRcoIntersection.intersection, Std.Roo.HasRcoIntersection.intersection]

public theorem mkSlice_roc_eq_mkSlice_roo_min {xs : Array α} {lo hi : Nat} :
    xs[lo<...=hi] = xs[(min (lo + 1) (min (hi + 1) xs.size))...(min (hi + 1) xs.size)] := by
  simp [mkSlice_rco_eq_mkSlice_rco_min]

@[simp]
public theorem toList_mkSlice_roc {xs : Array α} {lo hi : Nat} :
    xs[lo<...=hi].toList = (xs.toList.take (hi + 1)).drop (lo + 1) := by
  rw [mkSlice_roc_eq_mkSlice_roo, toList_mkSlice_roo]

@[simp]
public theorem mkSlice_roi_eq_mkSlice_rci {xs : Array α} {lo : Nat} :
    xs[lo<...*] = xs[(lo + 1)...*] := by
  simp [Std.Roi.Sliceable.mkSlice, Std.Roi.HasRcoIntersection.intersection,
    Std.Rci.Sliceable.mkSlice, Std.Rci.HasRcoIntersection.intersection]

public theorem mkSlice_roi_eq_mkSlice_roo {xs : Array α} {lo : Nat} :
    xs[lo<...*] = xs[lo<...xs.size] := by
  simp [mkSlice_rci_eq_mkSlice_rco]

public theorem mkSlice_roi_eq_mkSlice_roo_min {xs : Array α} {lo : Nat} :
    xs[lo<...*] = xs[(min (lo + 1) xs.size)...xs.size] := by
  simp [mkSlice_rco_eq_mkSlice_rco_min]

@[simp]
public theorem toList_mkSlice_roi {xs : Array α} {lo : Nat} :
    xs[lo<...*].toList = xs.toList.drop (lo + 1) := by
  rw [mkSlice_roi_eq_mkSlice_rci, toList_mkSlice_rci]

@[simp]
public theorem mkSlice_rio_eq_mkSlice_rco {xs : Array α} {hi : Nat} :
    xs[*...hi] = xs[0...hi] := by
  simp [Std.Rio.Sliceable.mkSlice, Std.Rio.HasRcoIntersection.intersection,
    Std.Rco.Sliceable.mkSlice, Std.Rco.HasRcoIntersection.intersection]

public theorem mkSlice_rio_eq_mkSlice_rio_min {xs : Array α} {hi : Nat} :
    xs[*...hi] = xs[*...(min hi xs.size)] := by
  simp [mkSlice_rco_eq_mkSlice_rco_min]

@[simp]
public theorem toList_mkSlice_rio {xs : Array α} {hi : Nat} :
    xs[*...hi].toList = xs.toList.take hi := by
  rw [mkSlice_rio_eq_mkSlice_rco, toList_mkSlice_rco, List.drop_zero]

@[simp]
public theorem mkSlice_ric_eq_mkSlice_rio {xs : Array α} {hi : Nat} :
    xs[*...=hi] = xs[*...(hi + 1)] := by
  simp [Std.Ric.Sliceable.mkSlice, Std.Rio.Sliceable.mkSlice,
    Std.Ric.HasRcoIntersection.intersection, Std.Rio.HasRcoIntersection.intersection]

public theorem mkSlice_ric_eq_mkSlice_rio_min {xs : Array α} {hi : Nat} :
    xs[*...=hi] = xs[*...(min (hi + 1) xs.size)] := by
  simp [mkSlice_rco_eq_mkSlice_rco_min]

@[simp]
public theorem toList_mkSlice_ric {xs : Array α} {hi : Nat} :
    xs[*...=hi].toList = xs.toList.take (hi + 1) := by
  rw [mkSlice_ric_eq_mkSlice_rio, toList_mkSlice_rio]

@[simp]
public theorem mkSlice_rii_eq_mkSlice_rci {xs : Array α} :
    xs[*...*] = xs[0...*] := by
  simp [Std.Rii.Sliceable.mkSlice, Std.Rci.Sliceable.mkSlice,
    Std.Rci.HasRcoIntersection.intersection]

public theorem mkSlice_rii_eq_mkSlice_rio {xs : Array α} :
    xs[*...*] = xs[*...xs.size] := by
  simp [mkSlice_rci_eq_mkSlice_rco]

public theorem mkSlice_rii_eq_mkSlice_rio_min {xs : Array α} :
    xs[*...*] = xs[*...xs.size] := by
  simp [mkSlice_rco_eq_mkSlice_rco_min]

@[simp]
public theorem toList_mkSlice_rii {xs : Array α} :
    xs[*...*].toList = xs.toList := by
  rw [mkSlice_rii_eq_mkSlice_rci, toList_mkSlice_rci, List.drop_zero]

end Array
