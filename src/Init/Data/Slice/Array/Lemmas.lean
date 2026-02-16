/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Slice.Array.Iterator
import all Init.Data.Array.Subarray
import all Init.Data.Slice.Array.Basic
import Init.Data.Slice.Lemmas
import all Init.Data.Slice.Array.Iterator
import all Init.Data.Slice.Operations
import all Init.Data.Range.Polymorphic.Iterators
import all Init.Data.Range.Polymorphic.Lemmas
import Init.Data.Slice.List.Lemmas
public import Init.Data.List.Control
public import Init.Data.Nat.MinMax
public import Init.Data.Slice.Array.Basic
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.TakeDrop
public import Init.Data.Array.Subarray.Split
import all Init.Data.Array.Subarray.Split
import Init.Data.Slice.InternalLemmas

open Std Std.Iterators Std.PRange Std.Slice

namespace SubarrayIterator

theorem step_eq {it : Iter (α := SubarrayIterator α) α} :
    it.step = if h : it.1.xs.start < it.1.xs.stop then
        haveI := it.1.xs.start_le_stop
        haveI := it.1.xs.stop_le_array_size
        ⟨.yield ⟨⟨it.1.xs.array, it.1.xs.start + 1, it.1.xs.stop, by omega, by assumption⟩⟩
            (it.1.xs.array[it.1.xs.start]'(by omega)),
          (by
            simp_all [Iter.IsPlausibleStep, IterM.IsPlausibleStep, Iterator.IsPlausibleStep,
              SubarrayIterator.step, Iter.toIterM])⟩
      else
        ⟨.done, (by
            simpa [Iter.IsPlausibleStep, IterM.IsPlausibleStep, Iterator.IsPlausibleStep,
              SubarrayIterator.step] using h)⟩ := by
  simp only [Iter.step, IterM.Step.toPure, Iter.toIter_toIterM, IterStep.mapIterator, IterM.step,
    Iterator.step, SubarrayIterator.step, Id.run_pure, Shrink.inflate_deflate]
  by_cases h : it.internalState.xs.start < it.internalState.xs.stop
  · simp only [h, ↓reduceDIte]
    split
    · rfl
    · rename_i h'
      exact h'.elim h
  · simp only [h, ↓reduceDIte]
    split
    · rename_i h'
      exact h.elim h'
    · rfl

theorem val_step_eq {it : Iter (α := SubarrayIterator α) α} :
    it.step.val = if h : it.1.xs.start < it.1.xs.stop then
        haveI := it.1.xs.start_le_stop
        haveI := it.1.xs.stop_le_array_size
        .yield ⟨⟨it.1.xs.array, it.1.xs.start + 1, it.1.xs.stop, by omega, by assumption⟩⟩
          it.1.xs.array[it.1.xs.start]
      else
        .done := by
  simp only [step_eq]
  split <;> simp

theorem toList_eq {α : Type u} {it : Iter (α := SubarrayIterator α) α} :
    it.toList =
      (it.internalState.xs.array.toList.take it.internalState.xs.stop).drop it.internalState.xs.start := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [Iter.toList_eq_match_step, SubarrayIterator.val_step_eq]
  by_cases h : it.internalState.xs.start < it.internalState.xs.stop
  · simp [h]
    have := it.1.xs.start_le_stop
    have := it.1.xs.stop_le_array_size
    rw [ihy (out := it.internalState.xs.array[it.internalState.xs.start])]
    · simp only [Subarray.start]
      rw (occs := [2]) [List.drop_eq_getElem_cons]; rotate_left
      · rw [List.length_take]
        simp [it.internalState.xs.stop_le_array_size]
        exact h
      · simp [Subarray.array, Subarray.stop]
    · simp only [Iter.IsPlausibleStep, IterM.IsPlausibleStep, Iterator.IsPlausibleStep,
      IterStep.mapIterator_yield, SubarrayIterator.step]
      rw [dif_pos]; rotate_left; exact h
      rfl
  · rw [dif_neg]; rotate_left; exact h
    simp_all [it.internalState.xs.stop_le_array_size]

theorem length_eq {α : Type u} {it : Iter (α := SubarrayIterator α) α} :
    it.length = it.internalState.xs.stop - it.internalState.xs.start := by
  simp [← Iter.length_toList_eq_length, toList_eq, it.internalState.xs.stop_le_array_size]

@[deprecated length_eq (since := "2026-01-28")]
def count_eq := @length_eq

end SubarrayIterator

namespace Subarray

theorem Internal.iter_eq {α : Type u} {s : Subarray α} :
    Internal.iter s = ⟨⟨s⟩⟩ :=
  rfl

theorem Internal.toList_iter {α : Type u} {s : Subarray α} :
    (Internal.iter s).toList =
      (s.array.toList.take s.stop).drop s.start := by
  simp [SubarrayIterator.toList_eq, Internal.iter_eq_toIteratorIter, ToIterator.iter_eq]

public instance : LawfulSliceSize (Internal.SubarrayData α) where
  lawful s := by
    simp [SliceSize.size, ToIterator.iter_eq,
      ← Iter.length_toList_eq_length, SubarrayIterator.toList_eq,
      s.internalRepresentation.stop_le_array_size, start, stop, array]

public theorem toArray_eq_sliceToArray {α : Type u} {s : Subarray α} :
    s.toArray = Slice.toArray s := by
  simp [Subarray.toArray]

@[simp]
public theorem forIn_toList {α : Type u} {s : Subarray α}
    {m : Type v → Type w} [Monad m] [LawfulMonad m] {γ : Type v} {init : γ}
    {f : α → γ → m (ForInStep γ)} :
    ForIn.forIn s.toList init f = ForIn.forIn s init f :=
  Slice.forIn_toList

@[grind =]
public theorem forIn_eq_forIn_toList {α : Type u} {s : Subarray α}
    {m : Type v → Type w} [Monad m] [LawfulMonad m] {γ : Type v} {init : γ}
    {f : α → γ → m (ForInStep γ)} :
    ForIn.forIn s init f = ForIn.forIn s.toList init f :=
  forIn_toList.symm

@[simp]
public theorem forIn_toArray {α : Type u} {s : Subarray α}
    {m : Type v → Type w} [Monad m] [LawfulMonad m] {γ : Type v} {init : γ}
    {f : α → γ → m (ForInStep γ)} :
    ForIn.forIn s.toArray init f = ForIn.forIn s init f :=
  Slice.forIn_toArray

public theorem sliceFoldlM_eq_foldlM {m} [Monad m] {α : Type u} {s : Subarray α}
    {f : β → α → m β} :
    s.foldlM (init := init) f = Slice.foldlM (s := s) (init := init) f :=
  (rfl)

public theorem sliceFoldl_eq_foldl {α : Type u} {s : Subarray α} {f : β → α → β} :
    s.foldl (init := init) f = Slice.foldl (s := s) (init := init) f :=
  (rfl)

public theorem foldlM_toList {m} [Monad m] {α : Type u} {s : Subarray α} {f}
    [LawfulMonad m] :
    s.toList.foldlM (init := init) f = s.foldlM (m := m) (init := init) f := by
  simp [Std.Slice.foldlM_toList, sliceFoldlM_eq_foldlM]

public theorem foldl_toList {α : Type u} {s : Subarray α} {f} :
    s.toList.foldl (init := init) f = s.foldl (init := init) f := by
  simp [Std.Slice.foldl_toList, sliceFoldl_eq_foldl]

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
        simp only [h, right_eq_dite_iff, Slice.mk.injEq, Internal.SubarrayData.mk.injEq, and_true,
          true_and]
        omega
      · simp only [ge_iff_le, not_false_eq_true, Nat.min_eq_right (Nat.le_of_not_ge _), *] at h
        simp [h]
        omega
  · split
    · split
      · simp only [not_false_eq_true, Nat.min_eq_right (Nat.le_of_not_ge _),
        Nat.min_eq_left, Nat.not_le, *] at *
        simp [*]; omega
      · simp
    · simp [Nat.min_eq_right (Nat.le_of_not_ge _), *] at h
      split
      · simp only [Nat.min_eq_left, *] at h
        simp [*]; omega
      · simp

public theorem Array.toSubarray_eq_min {xs : Array α} {lo hi : Nat} :
    xs.toSubarray lo hi = ⟨⟨xs, min lo (min hi xs.size), min hi xs.size, Nat.min_le_right _ _,
      Nat.min_le_right _ _⟩⟩ := by
  simp only [Array.toSubarray]
  split <;> split <;> simp [Nat.min_eq_right (Nat.le_of_not_ge _), *]

@[simp, grind =]
public theorem Array.array_toSubarray {xs : Array α} {lo hi : Nat} :
    (xs.toSubarray lo hi).array = xs := by
  simp [toSubarray_eq_min, Subarray.array]

@[simp, grind =]
public theorem Array.start_toSubarray {xs : Array α} {lo hi : Nat} :
    (xs.toSubarray lo hi).start = min lo (min hi xs.size) := by
  simp [toSubarray_eq_min, Subarray.start]

@[simp, grind =]
public theorem Array.stop_toSubarray {xs : Array α} {lo hi : Nat} :
    (xs.toSubarray lo hi).stop = min hi xs.size := by
  simp [toSubarray_eq_min, Subarray.stop]

public theorem Subarray.toList_eq {xs : Subarray α} :
    xs.toList = (xs.array.extract xs.start xs.stop).toList := by
  let aslice := xs
  obtain ⟨⟨array, start, stop, h₁, h₂⟩⟩ := xs
  let lslice : ListSlice α := ⟨array.toList.drop start, some (stop - start)⟩
  simp only [Subarray.start, Subarray.stop, Subarray.array]
  change aslice.toList = _
  have : aslice.toList = lslice.toList := by
    rw [ListSlice.toList_eq]
    simp +instances only [aslice, lslice, Std.Slice.toList, Internal.toList_iter]
    apply List.ext_getElem
    · have : stop - start ≤ array.size - start := by omega
      simp [Subarray.start, Subarray.stop, *, Subarray.array]
    · intros
      simp [Subarray.array, Subarray.start, Subarray.stop]
  simp +instances [this, ListSlice.toList_eq, lslice]

-- TODO: The current `List.extract_eq_drop_take` should be called `List.extract_eq_take_drop`
private theorem Std.Internal.List.extract_eq_drop_take' {l : List α} {start stop : Nat} :
    l.extract start stop = (l.take stop).drop start := by
  simp [List.take_drop]
  by_cases start ≤ stop
  · simp [*]
  · have h₁ : stop - start = 0 := by omega
    have h₂ : min stop l.length ≤ stop := by omega
    simp only [Nat.add_zero, List.drop_take_self, List.nil_eq, List.drop_eq_nil_iff,
      List.length_take, ge_iff_le, h₁]
    omega

public theorem Subarray.toList_eq_drop_take {xs : Subarray α} :
    xs.toList = (xs.array.toList.take xs.stop).drop xs.start := by
  rw [Subarray.toList_eq, Array.toList_extract, Std.Internal.List.extract_eq_drop_take']

@[grind =]
public theorem Subarray.size_eq {xs : Subarray α} :
    xs.size = xs.stop - xs.start := by
  simp [Subarray.size]

@[simp, grind =]
public theorem Subarray.size_drop {xs : Subarray α} :
    (xs.drop i).size = xs.size - i := by
  simp only [size, stop, drop, start]
  omega

@[simp, grind =]
public theorem Subarray.size_take {xs : Subarray α} :
    (xs.take i).size = min i xs.size := by
  simp only [size, stop, take, start]
  omega

public theorem Subarray.sliceSize_eq_size {xs : Subarray α} :
    Std.Slice.size xs = xs.size := by
  rfl

public theorem Subarray.getElem_eq_getElem_array {xs : Subarray α} {h : i < xs.size} :
    xs[i] = xs.array[xs.start + i]'(by simp only [size] at h; have := xs.stop_le_array_size; omega) := by
  rfl

public theorem Subarray.getElem_toList {xs : Subarray α} {h : i < xs.toList.length} :
    xs.toList[i]'h = xs[i]'(by simpa using h) := by
  simp [getElem_eq_getElem_array, toList_eq_drop_take]

public theorem Subarray.getElem_eq_getElem_toList {xs : Subarray α} {h : i < xs.size} :
    xs[i]'h = xs.toList[i]'(by simpa using h) := by
  rw [getElem_toList]

@[simp, grind =]
public theorem Subarray.toList_drop {xs : Subarray α} :
    (xs.drop n).toList = xs.toList.drop n := by
  simp [Subarray.toList_eq_drop_take, drop, start, stop, array]

@[simp, grind =]
public theorem Subarray.toList_take {xs : Subarray α} :
    (xs.take n).toList = xs.toList.take n := by
  simp [Subarray.toList_eq_drop_take, take, start, stop, array, List.take_drop, List.take_take]

@[simp, grind =]
public theorem Subarray.toArray_toList {xs : Subarray α} :
    xs.toList.toArray = xs.toArray := by
  simp [Std.Slice.toList, Subarray.toArray, Std.Slice.toArray]

@[simp, grind =]
public theorem Subarray.toList_toArray {xs : Subarray α} :
    xs.toArray.toList = xs.toList := by
  simp [Std.Slice.toList, Subarray.toArray, Std.Slice.toArray]

@[simp, grind =]
public theorem Subarray.length_toList {xs : Subarray α} :
    xs.toList.length = xs.size := by
  have : xs.start ≤ xs.stop := xs.internalRepresentation.start_le_stop
  have : xs.stop ≤ xs.array.size := xs.internalRepresentation.stop_le_array_size
  simp [Subarray.toList_eq, Subarray.size]; omega

@[simp, grind =]
public theorem Subarray.size_toArray {xs : Subarray α} :
    xs.toArray.size = xs.size := by
  simp [← Subarray.toArray_toList, Subarray.size, Slice.size, SliceSize.size, start, stop]

namespace Array

@[simp, grind =]
public theorem array_mkSlice_rco {xs : Array α} {lo hi : Nat} :
    xs[lo...hi].array = xs := by
  simp [Std.Rco.Sliceable.mkSlice, Array.toSubarray, apply_dite, Subarray.array]

@[simp, grind =]
public theorem start_mkSlice_rco {xs : Array α} {lo hi : Nat} :
    xs[lo...hi].start = min lo (min hi xs.size) := by
  simp [Std.Rco.Sliceable.mkSlice]

@[simp, grind =]
public theorem stop_mkSlice_rco {xs : Array α} {lo hi : Nat} :
    xs[lo...hi].stop = min hi xs.size := by
  simp [Std.Rco.Sliceable.mkSlice]

public theorem mkSlice_rco_eq_mkSlice_rco_min {xs : Array α} {lo hi : Nat} :
    xs[lo...hi] = xs[(min lo (min hi xs.size))...(min hi xs.size)] := by
  simp [Std.Rco.Sliceable.mkSlice, Array.toSubarray_eq_min]

@[simp, grind =]
public theorem toList_mkSlice_rco {xs : Array α} {lo hi : Nat} :
    xs[lo...hi].toList = (xs.toList.take hi).drop lo := by
  rw [List.take_eq_take_min, List.drop_eq_drop_min]
  simp [Std.Rco.Sliceable.mkSlice, Subarray.toList_eq, List.take_drop,
    Nat.add_sub_of_le (Nat.min_le_right _ _)]

@[simp, grind =]
public theorem toArray_mkSlice_rco {xs : Array α} {lo hi : Nat} :
    xs[lo...hi].toArray = xs.extract lo hi := by
  simp only [← Subarray.toArray_toList, toList_mkSlice_rco]
  rw [show xs = xs.toList.toArray by simp, List.extract_toArray, List.extract_eq_drop_take]
  simp only [List.take_drop, mk.injEq]
  by_cases h : lo ≤ hi
  · congr 1
    rw [List.take_eq_take_iff, Nat.add_sub_cancel' h]
  · rw [List.drop_eq_nil_of_le, List.drop_eq_nil_of_le]
    · simp; omega
    · simp; omega

@[simp, grind =]
public theorem size_mkSlice_rco {xs : Array α} {lo hi : Nat} :
    xs[lo...hi].size = min hi xs.size - lo := by
  simp [← Subarray.length_toList]

@[simp, grind =]
public theorem mkSlice_rcc_eq_mkSlice_rco {xs : Array α} {lo hi : Nat} :
    xs[lo...=hi] = xs[lo...(hi + 1)] := by
  simp [Std.Rcc.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice]

public theorem mkSlice_rcc_eq_mkSlice_rco_min {xs : Array α} {lo hi : Nat} :
    xs[lo...=hi] = xs[(min lo (min (hi + 1) xs.size))...(min (hi + 1) xs.size)] := by
  simp [mkSlice_rco_eq_mkSlice_rco_min]

@[simp, grind =]
public theorem array_mkSlice_rcc {xs : Array α} {lo hi : Nat} :
    xs[lo...=hi].array = xs := by
  simp [Std.Rcc.Sliceable.mkSlice, Array.toSubarray, apply_dite, Subarray.array]

@[simp, grind =]
public theorem start_mkSlice_rcc {xs : Array α} {lo hi : Nat} :
    xs[lo...=hi].start = min lo (min (hi + 1) xs.size) := by
  simp [Std.Rco.Sliceable.mkSlice]

@[simp, grind =]
public theorem stop_mkSlice_rcc {xs : Array α} {lo hi : Nat} :
    xs[lo...=hi].stop = min (hi + 1) xs.size := by
  simp [Std.Rco.Sliceable.mkSlice]

@[simp, grind =]
public theorem toList_mkSlice_rcc {xs : Array α} {lo hi : Nat} :
    xs[lo...=hi].toList = (xs.toList.take (hi + 1)).drop lo := by
  simp

@[simp, grind =]
public theorem toArray_mkSlice_rcc {xs : Array α} {lo hi : Nat} :
    xs[lo...=hi].toArray = xs.extract lo (hi + 1) := by
  simp

@[simp, grind =]
public theorem size_mkSlice_rcc {xs : Array α} {lo hi : Nat} :
    xs[lo...=hi].size = min (hi + 1) xs.size - lo := by
  simp [← Subarray.length_toList]

@[simp, grind =]
public theorem array_mkSlice_rci {xs : Array α} {lo : Nat} :
    xs[lo...*].array = xs := by
  simp [Std.Rci.Sliceable.mkSlice, Array.toSubarray, apply_dite, Subarray.array]

@[simp, grind =]
public theorem start_mkSlice_rci {xs : Array α} {lo : Nat} :
    xs[lo...*].start = min lo xs.size := by
  simp [Std.Rci.Sliceable.mkSlice, Std.Rci.HasRcoIntersection.intersection]

@[simp, grind =]
public theorem stop_mkSlice_rci {xs : Array α} {lo : Nat} :
    xs[lo...*].stop = xs.size := by
  simp [Std.Rci.Sliceable.mkSlice, Std.Rci.HasRcoIntersection.intersection]

public theorem mkSlice_rci_eq_mkSlice_rco {xs : Array α} {lo : Nat} :
    xs[lo...*] = xs[lo...xs.size] := by
  simp [Std.Rci.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice, Std.Rci.HasRcoIntersection.intersection]

public theorem mkSlice_rci_eq_mkSlice_rco_min {xs : Array α} {lo : Nat} :
    xs[lo...*] = xs[(min lo xs.size)...xs.size] := by
  simp [mkSlice_rci_eq_mkSlice_rco, mkSlice_rco_eq_mkSlice_rco_min]

@[simp, grind =]
public theorem toList_mkSlice_rci {xs : Array α} {lo : Nat} :
    xs[lo...*].toList = xs.toList.drop lo := by
  rw [mkSlice_rci_eq_mkSlice_rco, toList_mkSlice_rco, ← Array.length_toList, List.take_length]

@[simp, grind =]
public theorem toArray_mkSlice_rci {xs : Array α} {lo : Nat} :
    xs[lo...*].toArray = xs.extract lo := by
  simp [mkSlice_rci_eq_mkSlice_rco]

@[simp, grind =]
public theorem size_mkSlice_rci {xs : Array α} {lo : Nat} :
    xs[lo...*].size = xs.size - lo := by
  simp [← Subarray.length_toList]

@[simp, grind =]
public theorem array_mkSlice_roo {xs : Array α} {lo hi : Nat} :
    xs[lo<...hi].array = xs := by
  simp [Std.Roo.Sliceable.mkSlice, Array.toSubarray, apply_dite, Subarray.array]

@[simp, grind =]
public theorem start_mkSlice_roo {xs : Array α} {lo hi : Nat} :
    xs[lo<...hi].start = min (lo + 1) (min hi xs.size) := by
  simp [Std.Roo.Sliceable.mkSlice]

@[simp, grind =]
public theorem stop_mkSlice_roo {xs : Array α} {lo hi : Nat} :
    xs[lo<...hi].stop = min hi xs.size := by
  simp [Std.Roo.Sliceable.mkSlice]

public theorem mkSlice_roo_eq_mkSlice_rco {xs : Array α} {lo hi : Nat} :
    xs[lo<...hi] = xs[(lo + 1)...hi] := by
  simp [Std.Roo.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice]

public theorem mkSlice_roo_eq_mkSlice_roo_min {xs : Array α} {lo hi : Nat} :
    xs[lo<...hi] = xs[(min (lo + 1) (min hi xs.size))...(min hi xs.size)] := by
  simp [mkSlice_roo_eq_mkSlice_rco, mkSlice_rco_eq_mkSlice_rco_min]

@[simp, grind =]
public theorem toList_mkSlice_roo {xs : Array α} {lo hi : Nat} :
    xs[lo<...hi].toList = (xs.toList.take hi).drop (lo + 1) := by
  simp [mkSlice_roo_eq_mkSlice_rco]

@[simp, grind =]
public theorem toArray_mkSlice_roo {xs : Array α} {lo hi : Nat} :
    xs[lo<...hi].toArray = xs.extract (lo + 1) hi := by
  simp [mkSlice_roo_eq_mkSlice_rco]

@[simp, grind =]
public theorem size_mkSlice_roo {xs : Array α} {lo hi : Nat} :
    xs[lo<...hi].size = min hi xs.size - (lo + 1) := by
  simp [← Subarray.length_toList]

@[simp, grind =]
public theorem array_mkSlice_roc {xs : Array α} {lo hi : Nat} :
    xs[lo<...=hi].array = xs := by
  simp [Std.Roc.Sliceable.mkSlice, Array.toSubarray, apply_dite, Subarray.array]

@[simp, grind =]
public theorem start_mkSlice_roc {xs : Array α} {lo hi : Nat} :
    xs[lo<...=hi].start = min (lo + 1) (min (hi + 1) xs.size) := by
  simp [Std.Roc.Sliceable.mkSlice]

@[simp, grind =]
public theorem stop_mkSlice_roc {xs : Array α} {lo hi : Nat} :
    xs[lo<...=hi].stop = min (hi + 1) xs.size := by
  simp [Std.Roc.Sliceable.mkSlice]

public theorem mkSlice_roc_eq_mkSlice_roo {xs : Array α} {lo hi : Nat} :
    xs[lo<...=hi] = xs[lo<...(hi + 1)] := by
  simp [Std.Roc.Sliceable.mkSlice, Std.Roo.Sliceable.mkSlice]

public theorem mkSlice_roc_eq_mkSlice_rco {xs : Array α} {lo hi : Nat} :
    xs[lo<...=hi] = xs[(lo + 1)...(hi + 1)] := by
  simp [mkSlice_roc_eq_mkSlice_roo, mkSlice_roo_eq_mkSlice_rco]

public theorem mkSlice_roc_eq_mkSlice_roo_min {xs : Array α} {lo hi : Nat} :
    xs[lo<...=hi] = xs[(min (lo + 1) (min (hi + 1) xs.size))...(min (hi + 1) xs.size)] := by
  simp [mkSlice_roc_eq_mkSlice_rco, mkSlice_rco_eq_mkSlice_rco_min]

@[simp, grind =]
public theorem toList_mkSlice_roc {xs : Array α} {lo hi : Nat} :
    xs[lo<...=hi].toList = (xs.toList.take (hi + 1)).drop (lo + 1) := by
  simp [mkSlice_roc_eq_mkSlice_rco]

@[simp, grind =]
public theorem toArray_mkSlice_roc {xs : Array α} {lo hi : Nat} :
    xs[lo<...=hi].toArray = xs.extract (lo + 1) (hi + 1) := by
  simp [mkSlice_roc_eq_mkSlice_rco]

@[simp, grind =]
public theorem size_mkSlice_roc {xs : Array α} {lo hi : Nat} :
    xs[lo<...=hi].size = min (hi + 1) xs.size - (lo + 1) := by
  simp [← Subarray.length_toList]

@[simp, grind =]
public theorem array_mkSlice_roi {xs : Array α} {lo : Nat} :
    xs[lo<...*].array = xs := by
  simp [Std.Roi.Sliceable.mkSlice, Array.toSubarray, apply_dite, Subarray.array]

@[simp, grind =]
public theorem start_mkSlice_roi {xs : Array α} {lo : Nat} :
    xs[lo<...*].start = min (lo + 1) xs.size := by
  simp [Std.Roi.Sliceable.mkSlice, Std.Roi.HasRcoIntersection.intersection]

@[simp, grind =]
public theorem stop_mkSlice_roi {xs : Array α} {lo : Nat} :
    xs[lo<...*].stop = xs.size := by
  simp [Std.Roi.Sliceable.mkSlice, Std.Roi.HasRcoIntersection.intersection]

public theorem mkSlice_roi_eq_mkSlice_rci {xs : Array α} {lo : Nat} :
    xs[lo<...*] = xs[(lo + 1)...*] := by
  simp [Std.Roi.Sliceable.mkSlice, Std.Roi.HasRcoIntersection.intersection,
    Std.Rci.Sliceable.mkSlice, Std.Rci.HasRcoIntersection.intersection]

public theorem mkSlice_roi_eq_mkSlice_roo {xs : Array α} {lo : Nat} :
    xs[lo<...*] = xs[lo<...xs.size] := by
  simp [mkSlice_roi_eq_mkSlice_rci, mkSlice_rci_eq_mkSlice_rco,
    mkSlice_roo_eq_mkSlice_rco]

public theorem mkSlice_roi_eq_mkSlice_rco {xs : Array α} {lo : Nat} :
    xs[lo<...*] = xs[(lo + 1)...xs.size] := by
  simp [mkSlice_roi_eq_mkSlice_rci, mkSlice_rci_eq_mkSlice_rco]

public theorem mkSlice_roi_eq_mkSlice_roo_min {xs : Array α} {lo : Nat} :
    xs[lo<...*] = xs[(min (lo + 1) xs.size)...xs.size] := by
  simp [mkSlice_roi_eq_mkSlice_rco, mkSlice_rco_eq_mkSlice_rco_min]

@[simp, grind =]
public theorem toList_mkSlice_roi {xs : Array α} {lo : Nat} :
    xs[lo<...*].toList = xs.toList.drop (lo + 1) := by
  simp only [mkSlice_roi_eq_mkSlice_rci, toList_mkSlice_rci]

@[simp, grind =]
public theorem toArray_mkSlice_roi {xs : Array α} {lo : Nat} :
    xs[lo<...*].toArray = xs.drop (lo + 1) := by
  simp [mkSlice_roi_eq_mkSlice_rci]

@[simp, grind =]
public theorem size_mkSlice_roi {xs : Array α} {lo : Nat} :
    xs[lo<...*].size = xs.size - (lo + 1) := by
  simp [← Subarray.length_toList]

@[simp, grind =]
public theorem array_mkSlice_rio {xs : Array α} {hi : Nat} :
    xs[*...hi].array = xs := by
  simp [Std.Rio.Sliceable.mkSlice, Array.toSubarray, apply_dite, Subarray.array]

@[simp, grind =]
public theorem start_mkSlice_rio {xs : Array α} {hi : Nat} :
    xs[*...hi].start = 0 := by
  simp [Std.Rio.Sliceable.mkSlice]

@[simp, grind =]
public theorem stop_mkSlice_rio {xs : Array α} {hi : Nat} :
    xs[*...hi].stop = min hi xs.size := by
  simp [Std.Rio.Sliceable.mkSlice]

public theorem mkSlice_rio_eq_mkSlice_rco {xs : Array α} {hi : Nat} :
    xs[*...hi] = xs[0...hi] := by
  simp [Std.Rio.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice]

public theorem mkSlice_rio_eq_mkSlice_rio_min {xs : Array α} {hi : Nat} :
    xs[*...hi] = xs[*...(min hi xs.size)] := by
  simp [mkSlice_rio_eq_mkSlice_rco, mkSlice_rco_eq_mkSlice_rco_min]

@[simp, grind =]
public theorem toList_mkSlice_rio {xs : Array α} {hi : Nat} :
    xs[*...hi].toList = xs.toList.take hi := by
  simp [mkSlice_rio_eq_mkSlice_rco]

@[simp, grind =]
public theorem toArray_mkSlice_rio {xs : Array α} {hi : Nat} :
    xs[*...hi].toArray = xs.extract 0 hi := by
  simp [mkSlice_rio_eq_mkSlice_rco]

@[simp, grind =]
public theorem size_mkSlice_rio {xs : Array α} {hi : Nat} :
    xs[*...hi].size = min hi xs.size := by
  simp [← Subarray.length_toList]

@[simp, grind =]
public theorem array_mkSlice_ric {xs : Array α} {hi : Nat} :
    xs[*...=hi].array = xs := by
  simp [Std.Ric.Sliceable.mkSlice, Array.toSubarray, apply_dite, Subarray.array]

@[simp, grind =]
public theorem start_mkSlice_ric {xs : Array α} {hi : Nat} :
    xs[*...=hi].start = 0 := by
  simp [Std.Ric.Sliceable.mkSlice]

@[simp, grind =]
public theorem stop_mkSlice_ric {xs : Array α} {hi : Nat} :
    xs[*...=hi].stop = min (hi + 1) xs.size := by
  simp [Std.Ric.Sliceable.mkSlice]

public theorem mkSlice_ric_eq_mkSlice_rio {xs : Array α} {hi : Nat} :
    xs[*...=hi] = xs[*...(hi + 1)] := by
  simp [Std.Ric.Sliceable.mkSlice, Std.Rio.Sliceable.mkSlice]

public theorem mkSlice_ric_eq_mkSlice_rco {xs : Array α} {hi : Nat} :
    xs[*...=hi] = xs[0...(hi + 1)] := by
  simp [mkSlice_ric_eq_mkSlice_rio, mkSlice_rio_eq_mkSlice_rco]

public theorem mkSlice_ric_eq_mkSlice_rio_min {xs : Array α} {hi : Nat} :
    xs[*...=hi] = xs[*...(min (hi + 1) xs.size)] := by
  simp [mkSlice_ric_eq_mkSlice_rco, mkSlice_rco_eq_mkSlice_rco_min,
    mkSlice_rio_eq_mkSlice_rco]

@[simp, grind =]
public theorem toList_mkSlice_ric {xs : Array α} {hi : Nat} :
    xs[*...=hi].toList = xs.toList.take (hi + 1) := by
  simp [mkSlice_ric_eq_mkSlice_rco]

@[simp, grind =]
public theorem toArray_mkSlice_ric {xs : Array α} {hi : Nat} :
    xs[*...=hi].toArray = xs.extract 0 (hi + 1) := by
  simp [mkSlice_ric_eq_mkSlice_rco]

@[simp, grind =]
public theorem size_mkSlice_ric {xs : Array α} {hi : Nat} :
    xs[*...=hi].size = min (hi + 1) xs.size := by
  simp [← Subarray.length_toList]

public theorem mkSlice_rii_eq_mkSlice_rci {xs : Array α} :
    xs[*...*] = xs[0...*] := by
  simp [Std.Rii.Sliceable.mkSlice, Std.Rci.Sliceable.mkSlice,
    Std.Rci.HasRcoIntersection.intersection]

public theorem mkSlice_rii_eq_mkSlice_rio {xs : Array α} :
    xs[*...*] = xs[*...xs.size] := by
  simp [mkSlice_rii_eq_mkSlice_rci, mkSlice_rci_eq_mkSlice_rco, mkSlice_rio_eq_mkSlice_rco]

public theorem mkSlice_rii_eq_mkSlice_rco {xs : Array α} :
    xs[*...*] = xs[0...xs.size] := by
  simp [mkSlice_rii_eq_mkSlice_rio, mkSlice_rio_eq_mkSlice_rco]

public theorem mkSlice_rii_eq_mkSlice_rio_min {xs : Array α} :
    xs[*...*] = xs[*...xs.size] := by
  simp [mkSlice_rii_eq_mkSlice_rco, mkSlice_rco_eq_mkSlice_rco_min, mkSlice_rio_eq_mkSlice_rco]

@[simp, grind =]
public theorem toList_mkSlice_rii {xs : Array α} :
    xs[*...*].toList = xs.toList := by
  rw [mkSlice_rii_eq_mkSlice_rci, toList_mkSlice_rci, List.drop_zero]

@[simp, grind =]
public theorem toArray_mkSlice_rii {xs : Array α} :
    xs[*...*].toArray = xs := by
  simp [mkSlice_rii_eq_mkSlice_rco]

@[simp, grind =]
public theorem size_mkSlice_rii {xs : Array α} :
    xs[*...*].size = xs.size := by
  simp [← Subarray.length_toList]

@[simp, grind =]
public theorem array_mkSlice_rii {xs : Array α} :
    xs[*...*].array = xs := by
  simp [mkSlice_rii_eq_mkSlice_rco]

@[simp, grind =]
public theorem start_mkSlice_rii {xs : Array α} :
    xs[*...*].start = 0 := by
  simp [mkSlice_rii_eq_mkSlice_rco]

@[simp, grind =]
public theorem stop_mkSlice_rii {xs : Array α} :
    xs[*...*].stop = xs.size := by
  simp [Std.Rii.Sliceable.mkSlice]

end Array

section SubarraySlices

namespace Subarray

@[simp, grind =]
public theorem toList_mkSlice_rco {xs : Subarray α} {lo hi : Nat} :
    xs[lo...hi].toList = (xs.toList.take hi).drop lo := by
  simp only [Std.Rco.Sliceable.mkSlice, Std.Rco.HasRcoIntersection.intersection, toList_eq,
    Array.start_toSubarray, Array.stop_toSubarray, Array.toList_extract, List.take_drop,
    List.take_take]
  rw [Nat.add_sub_cancel' (by omega)]
  simp [Subarray.size, ← Array.length_toList, ← List.take_eq_take_min, Nat.add_comm xs.start]

@[simp, grind =]
public theorem toArray_mkSlice_rco {xs : Subarray α} {lo hi : Nat} :
    xs[lo...hi].toArray = xs.toArray.extract lo hi := by
  simp [← Subarray.toArray_toList, Std.Internal.List.extract_eq_drop_take']

@[simp, grind =]
public theorem size_mkSlice_rco {xs : Subarray α} {lo hi : Nat} :
    xs[lo...hi].size = min hi xs.size - lo := by
  simp [← Subarray.length_toList]

public theorem mkSlice_rcc_eq_mkSlice_rco {xs : Subarray α} {lo hi : Nat} :
    xs[lo...=hi] = xs[lo...(hi + 1)] := by
  simp [Rcc.Sliceable.mkSlice, Rco.Sliceable.mkSlice,
    Rcc.HasRcoIntersection.intersection, Rco.HasRcoIntersection.intersection]

@[simp, grind =]
public theorem toList_mkSlice_rcc {xs : Subarray α} {lo hi : Nat} :
    xs[lo...=hi].toList = (xs.toList.take (hi + 1)).drop lo := by
  simp [mkSlice_rcc_eq_mkSlice_rco]

@[simp, grind =]
public theorem toArray_mkSlice_rcc {xs : Subarray α} {lo hi : Nat} :
    xs[lo...=hi].toArray = xs.toArray.extract lo (hi + 1) := by
  simp [mkSlice_rcc_eq_mkSlice_rco]

@[simp, grind =]
public theorem size_mkSlice_rcc {xs : Subarray α} {lo hi : Nat} :
    xs[lo...=hi].size = min (hi + 1) xs.size - lo := by
  simp [← Subarray.length_toList]

public theorem mkSlice_rci_eq_mkSlice_rco {xs : Subarray α} {lo : Nat} :
    xs[lo...*] = xs[lo...xs.size] := by
  simp [Rci.Sliceable.mkSlice, Rco.Sliceable.mkSlice,
    Rci.HasRcoIntersection.intersection, Rco.HasRcoIntersection.intersection]

@[simp, grind =]
public theorem toList_mkSlice_rci {xs : Subarray α} {lo : Nat} :
    xs[lo...*].toList = xs.toList.drop lo := by
  rw [mkSlice_rci_eq_mkSlice_rco, toList_mkSlice_rco, ← Subarray.length_toList, List.take_length]

@[simp, grind =]
public theorem toArray_mkSlice_rci {xs : Subarray α} {lo : Nat} :
    xs[lo...*].toArray = xs.toArray.extract lo := by
  simp [mkSlice_rci_eq_mkSlice_rco]

@[simp, grind =]
public theorem size_mkSlice_rci {xs : Subarray α} {lo : Nat} :
    xs[lo...*].size = xs.size - lo := by
  simp [← Subarray.length_toList]

public theorem mkSlice_roc_eq_mkSlice_roo {xs : Subarray α} {lo hi : Nat} :
    xs[lo<...=hi] = xs[lo<...(hi + 1)] := by
  simp [Std.Roc.Sliceable.mkSlice, Std.Roo.Sliceable.mkSlice,
    Std.Roc.HasRcoIntersection.intersection, Std.Roo.HasRcoIntersection.intersection]

public theorem mkSlice_roo_eq_mkSlice_rco {xs : Subarray α} {lo hi : Nat} :
    xs[lo<...hi] = xs[(lo + 1)...hi] := by
  simp [Std.Roo.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice,
    Std.Roo.HasRcoIntersection.intersection, Std.Rco.HasRcoIntersection.intersection]

public theorem mkSlice_roc_eq_mkSlice_rco {xs : Subarray α} {lo hi : Nat} :
    xs[lo<...=hi] = xs[(lo + 1)...(hi + 1)] := by
  simp [mkSlice_roc_eq_mkSlice_roo, mkSlice_roo_eq_mkSlice_rco]

@[simp, grind =]
public theorem toList_mkSlice_roo {xs : Subarray α} {lo hi : Nat} :
    xs[lo<...hi].toList = (xs.toList.take hi).drop (lo + 1) := by
  simp [mkSlice_roo_eq_mkSlice_rco]

@[simp, grind =]
public theorem toArray_mkSlice_roo {xs : Subarray α} {lo hi : Nat} :
    xs[lo<...hi].toArray = xs.toArray.extract (lo + 1) hi := by
  simp [mkSlice_roo_eq_mkSlice_rco]

@[simp, grind =]
public theorem size_mkSlice_roo {xs : Subarray α} {lo hi : Nat} :
    xs[lo<...hi].size = min hi xs.size - (lo + 1) := by
  simp [← Subarray.length_toList]

public theorem mkSlice_roc_eq_mkSlice_rcc {xs : Subarray α} {lo hi : Nat} :
    xs[lo<...=hi] = xs[(lo + 1)...=hi] := by
  simp [mkSlice_roc_eq_mkSlice_rco, mkSlice_rcc_eq_mkSlice_rco]

@[simp, grind =]
public theorem toList_mkSlice_roc {xs : Subarray α} {lo hi : Nat} :
    xs[lo<...=hi].toList = (xs.toList.take (hi + 1)).drop (lo + 1) := by
  simp [mkSlice_roc_eq_mkSlice_rco]

@[simp, grind =]
public theorem toArray_mkSlice_roc {xs : Subarray α} {lo hi : Nat} :
    xs[lo<...=hi].toArray = xs.toArray.extract (lo + 1) (hi + 1) := by
  simp [mkSlice_roc_eq_mkSlice_rco]

@[simp, grind =]
public theorem size_mkSlice_roc {xs : Subarray α} {lo hi : Nat} :
    xs[lo<...=hi].size = min (hi + 1) xs.size - (lo + 1) := by
  simp [← Subarray.length_toList]

public theorem mkSlice_roi_eq_mkSlice_rci {xs : Subarray α} {lo : Nat} :
    xs[lo<...*] = xs[(lo + 1)...*] := by
  simp [Std.Roi.Sliceable.mkSlice, Std.Rci.Sliceable.mkSlice,
    Std.Roi.HasRcoIntersection.intersection, Std.Rci.HasRcoIntersection.intersection]

public theorem mkSlice_roi_eq_mkSlice_rco {xs : Subarray α} {lo : Nat} :
    xs[lo<...*] = xs[(lo + 1)...xs.size] := by
  simp [mkSlice_roi_eq_mkSlice_rci, mkSlice_rci_eq_mkSlice_rco]

@[simp, grind =]
public theorem toList_mkSlice_roi {xs : Subarray α} {lo : Nat} :
    xs[lo<...*].toList = xs.toList.drop (lo + 1) := by
  rw [mkSlice_roi_eq_mkSlice_rci, toList_mkSlice_rci]

@[simp, grind =]
public theorem toArray_mkSlice_roi {xs : Subarray α} {lo : Nat} :
    xs[lo<...*].toArray = xs.toArray.extract (lo + 1) := by
  simp [mkSlice_roi_eq_mkSlice_rco]

@[simp, grind =]
public theorem size_mkSlice_roi {xs : Subarray α} {lo : Nat} :
    xs[lo<...*].size = xs.size - (lo + 1) := by
  simp [← Subarray.length_toList]

public theorem mkSlice_ric_eq_mkSlice_rio {xs : Subarray α} {hi : Nat} :
    xs[*...=hi] = xs[*...(hi + 1)] := by
  simp [Std.Ric.Sliceable.mkSlice, Std.Rio.Sliceable.mkSlice,
    Std.Ric.HasRcoIntersection.intersection, Std.Rio.HasRcoIntersection.intersection]

public theorem mkSlice_rio_eq_mkSlice_rco {xs : Subarray α} {hi : Nat} :
    xs[*...hi] = xs[0...hi] := by
  simp [Std.Rio.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice,
    Std.Rio.HasRcoIntersection.intersection, Std.Rco.HasRcoIntersection.intersection]

public theorem mkSlice_ric_eq_mkSlice_rco {xs : Subarray α} {hi : Nat} :
    xs[*...=hi] = xs[0...(hi + 1)] := by
  simp [mkSlice_ric_eq_mkSlice_rio, mkSlice_rio_eq_mkSlice_rco]

@[simp, grind =]
public theorem toList_mkSlice_rio {xs : Subarray α} {hi : Nat} :
    xs[*...hi].toList = xs.toList.take hi := by
  simp [mkSlice_rio_eq_mkSlice_rco]

@[simp, grind =]
public theorem toArray_mkSlice_rio {xs : Subarray α} {hi : Nat} :
    xs[*...hi].toArray = xs.toArray.extract 0 hi := by
  simp [mkSlice_rio_eq_mkSlice_rco]

@[simp, grind =]
public theorem size_mkSlice_rio {xs : Subarray α} {hi : Nat} :
    xs[*...hi].size = min hi xs.size := by
  simp [← Subarray.length_toList]

public theorem mkSlice_ric_eq_mkSlice_rcc {xs : Subarray α} {hi : Nat} :
    xs[*...=hi] = xs[0...=hi] := by
  simp [Std.Ric.Sliceable.mkSlice, Std.Rco.Sliceable.mkSlice,
    Std.Ric.HasRcoIntersection.intersection, Std.Rcc.HasRcoIntersection.intersection,
    Rcc.Sliceable.mkSlice]

@[simp, grind =]
public theorem toList_mkSlice_ric {xs : Subarray α} {hi : Nat} :
    xs[*...=hi].toList = xs.toList.take (hi + 1) := by
  simp [mkSlice_ric_eq_mkSlice_rco]

@[simp, grind =]
public theorem toArray_mkSlice_ric {xs : Subarray α} {hi : Nat} :
    xs[*...=hi].toArray = xs.toArray.extract 0 (hi + 1) := by
  simp [mkSlice_ric_eq_mkSlice_rco]

@[simp, grind =]
public theorem size_mkSlice_ric {xs : Subarray α} {hi : Nat} :
    xs[*...=hi].size = min (hi + 1) xs.size := by
  simp [← Subarray.length_toList]

@[simp, grind =, grind =]
public theorem mkSlice_rii {xs : Subarray α} :
    xs[*...*] = xs := by
  simp [Std.Rii.Sliceable.mkSlice]

end Subarray

end SubarraySlices
