/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators
import Init.Data.Iterators.Lemmas.Consumers.Collect
public import Init.Data.Range.Polymorphic.Basic
import all Init.Data.Range.Polymorphic.Basic
public import Init.Data.Range.Polymorphic.RangeIterator
import all Init.Data.Range.Polymorphic.RangeIterator
public import Init.Data.Range.Polymorphic.Iterators
import all Init.Data.Range.Polymorphic.Iterators
public import Init.Data.Iterators.Consumers.Loop
import all Init.Data.Iterators.Consumers.Loop
import Init.Data.Array.Monadic

public section

/-!
# Lemmas about ranges

This file provides lemmas about `Std.PRange`.
-/

namespace Std.PRange
open Std.Iterators

variable {shape : RangeShape} {α : Type u}

private theorem Internal.iter_Rox_eq_iter_Rcx_of_isSome_succ? {su} [UpwardEnumerable α]
    [SupportsUpperBound su α] [HasFiniteRanges su α]
    [LawfulUpwardEnumerable α]
    {lo : Bound .open α} {hi} (h : (UpwardEnumerable.succ? lo).isSome) :
    Internal.iter (PRange.mk (shape := ⟨.open, su⟩) lo hi) =
      Internal.iter (PRange.mk (shape := ⟨.closed, su⟩) (UpwardEnumerable.succ? lo |>.get h) hi) := by
  simp [Internal.iter, init?]

private theorem Internal.toList_eq_toList_iter {sl su} [UpwardEnumerable α]
    [BoundedUpwardEnumerable sl α] [SupportsUpperBound su α] [HasFiniteRanges su α]
    [LawfulUpwardEnumerable α] {r : PRange ⟨sl, su⟩ α} :
    r.toList = (Internal.iter r).toList := by
  rfl

private theorem Internal.toArray_eq_toArray_iter {sl su} [UpwardEnumerable α]
    [BoundedUpwardEnumerable sl α] [SupportsUpperBound su α] [HasFiniteRanges su α]
    [LawfulUpwardEnumerable α] {r : PRange ⟨sl, su⟩ α} :
    r.toArray = (Internal.iter r).toArray := by
  rfl

public theorem RangeIterator.toList_eq_match {su} [UpwardEnumerable α]
    [SupportsUpperBound su α] [HasFiniteRanges su α]
    [LawfulUpwardEnumerable α]
    {it : Iter (α := RangeIterator su α) α} :
    it.toList =  match it.internalState.next with
      | none => []
      | some a => if SupportsUpperBound.IsSatisfied it.internalState.upperBound a then
          a :: (⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩ : Iter (α := RangeIterator su α) α).toList
        else
          [] := by
  apply Eq.symm
  rw [Iter.toList_eq_match_step, RangeIterator.step_eq_step]
  simp only [RangeIterator.step]
  split <;> rename_i heq
  · simp [*]
  · split <;> rename_i heq' <;> simp [*]

public theorem RangeIterator.toArray_eq_match {su} [UpwardEnumerable α]
    [SupportsUpperBound su α] [HasFiniteRanges su α]
    [LawfulUpwardEnumerable α]
    {it : Iter (α := RangeIterator su α) α} :
    it.toArray =  match it.internalState.next with
      | none => #[]
      | some a => if SupportsUpperBound.IsSatisfied it.internalState.upperBound a then
          #[a] ++ (⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩ : Iter (α := RangeIterator su α) α).toArray
        else
          #[] := by
  rw [← Iter.toArray_toList, toList_eq_match]
  split
  · rfl
  · split <;> simp

@[simp]
public theorem toList_toArray {sl su} [UpwardEnumerable α] [BoundedUpwardEnumerable sl α]
    [SupportsUpperBound su α] [HasFiniteRanges su α] [LawfulUpwardEnumerable α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toArray.toList = r.toList := by
  simp [Internal.toArray_eq_toArray_iter, Internal.toList_eq_toList_iter]

@[simp]
public theorem toArray_toList {sl su} [UpwardEnumerable α] [BoundedUpwardEnumerable sl α]
    [SupportsUpperBound su α] [HasFiniteRanges su α] [LawfulUpwardEnumerable α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList.toArray = r.toArray := by
  simp [Internal.toArray_eq_toArray_iter, Internal.toList_eq_toList_iter]

public theorem toList_eq_match {sl su} [UpwardEnumerable α] [BoundedUpwardEnumerable sl α]
    [SupportsUpperBound su α] [HasFiniteRanges su α]
    [LawfulUpwardEnumerable α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList = match init? r.lower with
      | none => []
      | some a => if SupportsUpperBound.IsSatisfied r.upper a then
        a :: (PRange.mk (shape := ⟨.open, su⟩) a r.upper).toList
      else
        [] := by
  rw [Internal.toList_eq_toList_iter, RangeIterator.toList_eq_match]; rfl

public theorem toArray_eq_match {sl su} [UpwardEnumerable α] [BoundedUpwardEnumerable sl α]
    [SupportsUpperBound su α] [HasFiniteRanges su α]
    [LawfulUpwardEnumerable α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toArray = match init? r.lower with
      | none => #[]
      | some a => if SupportsUpperBound.IsSatisfied r.upper a then
        #[a] ++ (PRange.mk (shape := ⟨.open, su⟩) a r.upper).toArray
      else
        #[] := by
  rw [Internal.toArray_eq_toArray_iter, RangeIterator.toArray_eq_match]; rfl

public theorem toList_Rox_eq_toList_Rcx_of_isSome_succ? {su} [UpwardEnumerable α]
    [SupportsUpperBound su α] [HasFiniteRanges su α]
    [LawfulUpwardEnumerable α]
    {lo : Bound .open α} {hi} (h : (UpwardEnumerable.succ? lo).isSome) :
    (PRange.mk (shape := ⟨.open, su⟩) lo hi).toList =
      (PRange.mk (shape := ⟨.closed, su⟩) (UpwardEnumerable.succ? lo |>.get h) hi).toList := by
  simp [Internal.toList_eq_toList_iter, Internal.iter_Rox_eq_iter_Rcx_of_isSome_succ?, h]

@[deprecated toList_Rox_eq_toList_Rcx_of_isSome_succ? (since := "2025-08-22")]
public theorem toList_open_eq_toList_closed_of_isSome_succ? {su} [UpwardEnumerable α]
    [SupportsUpperBound su α] [HasFiniteRanges su α]
    [LawfulUpwardEnumerable α]
    {lo : Bound .open α} {hi} (h : (UpwardEnumerable.succ? lo).isSome) :
    (PRange.mk (shape := ⟨.open, su⟩) lo hi).toList =
      (PRange.mk (shape := ⟨.closed, su⟩) (UpwardEnumerable.succ? lo |>.get h) hi).toList :=
  toList_Rox_eq_toList_Rcx_of_isSome_succ? h

public theorem toArray_Rox_eq_toList_Rcx_of_isSome_succ? {su} [UpwardEnumerable α]
    [SupportsUpperBound su α] [HasFiniteRanges su α]
    [LawfulUpwardEnumerable α]
    {lo : Bound .open α} {hi} (h : (UpwardEnumerable.succ? lo).isSome) :
    (PRange.mk (shape := ⟨.open, su⟩) lo hi).toArray =
      (PRange.mk (shape := ⟨.closed, su⟩) (UpwardEnumerable.succ? lo |>.get h) hi).toArray := by
  simp [Internal.toArray_eq_toArray_iter, Internal.iter_Rox_eq_iter_Rcx_of_isSome_succ?, h]

public theorem toList_eq_nil_iff {sl su} [UpwardEnumerable α]
    [SupportsUpperBound su α] [HasFiniteRanges su α] [BoundedUpwardEnumerable sl α]
    [LawfulUpwardEnumerable α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList = [] ↔
      ¬ (∃ a, init? r.lower = some a ∧ SupportsUpperBound.IsSatisfied r.upper a) := by
  rw [Internal.toList_eq_toList_iter]
  rw [RangeIterator.toList_eq_match, Internal.iter]
  simp only
  split <;> rename_i heq <;> simp [heq]

public theorem toArray_eq_empty_iff {sl su} [UpwardEnumerable α]
    [SupportsUpperBound su α] [HasFiniteRanges su α] [BoundedUpwardEnumerable sl α]
    [LawfulUpwardEnumerable α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toArray = #[] ↔
      ¬ (∃ a, init? r.lower = some a ∧ SupportsUpperBound.IsSatisfied r.upper a) := by
  rw [← toArray_toList, List.toArray_eq_iff, Array.toList_empty, toList_eq_nil_iff]

public theorem mem_toList_iff_mem {sl su} [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α}
    {a : α} : a ∈ r.toList ↔ a ∈ r := by
  rw [Internal.toList_eq_toList_iter, Iter.mem_toList_iff_isPlausibleIndirectOutput,
    Internal.isPlausibleIndirectOutput_iter_iff]

public theorem mem_toArray_iff_mem {sl su} [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α}
    {a : α} : a ∈ r.toArray ↔ a ∈ r := by
  rw [Internal.toArray_eq_toArray_iter, Iter.mem_toArray_iff_isPlausibleIndirectOutput,
    Internal.isPlausibleIndirectOutput_iter_iff]

public theorem BoundedUpwardEnumerable.init?_succ?_closed [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] {lower lower' : Bound .closed α}
    (h : UpwardEnumerable.succ? lower = some lower') :
    init? lower' = (init? lower).bind UpwardEnumerable.succ? := by
  cases h : init? lower <;> rename_i ilower <;> cases h' : init? lower' <;> rename_i ilower'
  · simp
  · simp [init?] at h
  · simp [init?] at h'
  · simp_all [init?]

@[deprecated BoundedUpwardEnumerable.init?_succ?_closed (since := "2025-08-22")]
public theorem BoundedUpwardEnumerable.Closed.init?_succ [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] {lower lower' : Bound .closed α}
    (h : UpwardEnumerable.succ? lower = some lower') :
    init? lower' = (init? lower).bind UpwardEnumerable.succ? :=
  init?_succ?_closed h

public theorem pairwise_toList_upwardEnumerableLt {sl su} [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList.Pairwise (fun a b => UpwardEnumerable.LT a b) := by
  rw [Internal.toList_eq_toList_iter]
  generalize Internal.iter r = it
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [RangeIterator.toList_eq_match]
  repeat' split <;> (try exact .nil; done)
  rename_i a _ _
  apply List.Pairwise.cons
  · intro a' ha
    rw [Iter.mem_toList_iff_isPlausibleIndirectOutput] at ha
    replace ha := RangeIterator.upwardEnumerableLe_of_isPlausibleIndirectOutput ha
    simp only at ha
    have : UpwardEnumerable.LT a ha.choose := by
      refine ⟨0, ?_⟩
      simp only [succMany?_succ?, succMany?_zero,
        Option.bind_some]
      exact ha.choose_spec.1
    exact UpwardEnumerable.lt_of_lt_of_le this ha.choose_spec.2
  · apply ihy (out := a)
    simp_all [RangeIterator.isPlausibleStep_iff, RangeIterator.step]

public theorem pairwise_toList_ne {sl su} [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList.Pairwise (fun a b => a ≠ b) :=
  List.Pairwise.imp (fun hlt => UpwardEnumerable.ne_of_lt hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_lt {sl su} [LT α] [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList.Pairwise (fun a b => a < b) :=
  List.Pairwise.imp
    (fun hlt => (LawfulUpwardEnumerableLT.lt_iff ..).mpr hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_le {sl su} [LE α] [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList.Pairwise (fun a b => a ≤ b) :=
  pairwise_toList_upwardEnumerableLt
    |> List.Pairwise.imp UpwardEnumerable.le_of_lt
    |> List.Pairwise.imp (fun hle => (UpwardEnumerable.le_iff ..).mpr hle)

public theorem mem_Rco_succ_succ_iff [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [InfinitelyUpwardEnumerable α] [SupportsUpperBound .open α]
    [SupportsLowerBound .closed α] [LawfulUpwardEnumerableLowerBound .closed α]
    [HasFiniteRanges .open α] [LawfulUpwardEnumerable α] [LawfulOpenUpperBound α]
    {lower : Bound .closed α} {upper : Bound .open α} {a : α} :
    (a ∈ (succ lower)...(succ upper)) ↔ ∃ a', a = succ a' ∧ a' ∈ lower...upper := by
  simp [Membership.mem, LawfulUpwardEnumerableLowerBound.isSatisfied_iff,
    init?, LawfulOpenUpperBound.isSatisfied_iff_le]
  rw [← Option.some_get (InfinitelyUpwardEnumerable.isSome_succ? _)]
  simp only [Option.some.injEq, ← UpwardEnumerable.succ.eq_def]
  simp
  constructor
  · rintro ⟨⟨n, hn⟩, h⟩
    rw [succMany?_eq_some_iff_succMany, ← succMany_one, ← succMany_add, Nat.add_comm, succMany_add,
      succMany_one] at hn
    rw [← hn]
    refine ⟨succMany n lower, rfl, ?_, ?_⟩
    · exact ⟨n, by simp [succMany_eq_get]⟩
    · obtain ⟨m, hm⟩ := h
      refine ⟨m, ?_⟩
      rw [succMany?_eq_some_iff_succMany] at hm ⊢
      rwa [← hn, ← succMany_one, ← succMany_add, Nat.add_comm, succMany_add, succMany_one,
        succ_eq_succ_iff] at hm
  · rintro ⟨a', rfl, hl, hu⟩
    simp [UpwardEnumerable.succ_le_succ_iff, UpwardEnumerable.succ_lt_succ_iff]
    exact ⟨hl, hu⟩

@[deprecated mem_Rco_succ_succ_iff (since := "2025-08-22")]
public theorem ClosedOpen.mem_succ_iff [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [InfinitelyUpwardEnumerable α] [SupportsUpperBound .open α]
    [SupportsLowerBound .closed α] [LawfulUpwardEnumerableLowerBound .closed α]
    [HasFiniteRanges .open α] [LawfulUpwardEnumerable α] [LawfulOpenUpperBound α]
    {lower : Bound .closed α} {upper : Bound .open α} {a : α} :
    (a ∈ (succ lower)...(succ upper)) ↔ ∃ a', a = succ a' ∧ a' ∈ lower...upper :=
  mem_Rco_succ_succ_iff

private theorem eq_of_pairwise_lt_of_mem_iff_mem {lt : α → α → Prop} [asymm : Asymm lt]
    {l l' : List α} (hl : l.Pairwise lt) (hl' : l'.Pairwise lt)
    (h : ∀ a, a ∈ l ↔ a ∈ l') : l = l' := by
  induction l generalizing l'
  · cases l'
    · rfl
    · rename_i x xs
      specialize h x
      simp at h
  · rename_i x xs ih
    cases l'
    · specialize h x
      simp at h
    · have hx := (h x).mp (List.mem_cons_self)
      cases List.mem_cons.mp hx
      · rename_i y ys heq
        cases heq
        simp only [List.cons.injEq, true_and]
        apply ih hl.tail hl'.tail
        intro a
        specialize h a
        constructor
        · intro haxs
          replace h := h.mp (List.mem_cons_of_mem _ haxs)
          cases List.mem_cons.mp h
          · rename_i heq
            cases heq
            simp only [List.pairwise_cons] at hl
            have := hl.1 x haxs
            cases Asymm.asymm _ _ this this
          · simp [*]
        · intro hays
          replace h := h.mpr (List.mem_cons_of_mem _ hays)
          cases List.mem_cons.mp h
          · rename_i heq
            cases heq
            simp only [List.pairwise_cons] at hl'
            have := hl'.1 x hays
            cases Asymm.asymm _ _ this this
          · simp [*]
      · rename_i y ys hx
        simp only [List.pairwise_cons] at hl'
        have hlt := hl'.1 _ hx
        have hmem : y ∈ x :: xs := (h y).mpr List.mem_cons_self
        cases List.mem_cons.mp hmem
        · rename_i heq
          cases heq
          cases Asymm.asymm _ _ hlt hlt
        · simp only [List.pairwise_cons] at hl
          have hgt := hl.1 y ‹_›
          cases Asymm.asymm _ _ hlt hgt

public theorem toList_Rco_succ_succ_eq_map [UpwardEnumerable α] [SupportsLowerBound .closed α]
    [LinearlyUpwardEnumerable α] [InfinitelyUpwardEnumerable α] [SupportsUpperBound .open α]
    [HasFiniteRanges .open α] [LawfulUpwardEnumerable α] [LawfulOpenUpperBound α]
    [LawfulUpwardEnumerableLowerBound .closed α] [LawfulUpwardEnumerableUpperBound .open α]
    {lower : Bound .closed α} {upper : Bound .open α} :
    ((succ lower)...(succ upper)).toList =
      (lower...upper).toList.map succ := by
  apply eq_of_pairwise_lt_of_mem_iff_mem (lt := UpwardEnumerable.LT) (asymm := ?_)
  · apply pairwise_toList_upwardEnumerableLt
  · apply List.Pairwise.map (R := UpwardEnumerable.LT) (S := UpwardEnumerable.LT)
    · intro a b
      exact UpwardEnumerable.succ_lt_succ_iff.mpr
    · apply pairwise_toList_upwardEnumerableLt
  · simp only [List.mem_map, mem_toList_iff_mem]
    intro a
    rw [mem_Rco_succ_succ_iff]
    constructor
    · rintro ⟨a, rfl, h⟩
      exact ⟨a, h, rfl⟩
    · rintro ⟨a, h, h'⟩
      exact ⟨_, h'.symm, h⟩
  · exact ⟨fun _ _ => UpwardEnumerable.not_gt_of_lt⟩

@[deprecated toList_Rco_succ_succ_eq_map (since := "2025-08-22")]
public theorem ClosedOpen.toList_succ_succ_eq_map [UpwardEnumerable α] [SupportsLowerBound .closed α]
    [LinearlyUpwardEnumerable α] [InfinitelyUpwardEnumerable α] [SupportsUpperBound .open α]
    [HasFiniteRanges .open α] [LawfulUpwardEnumerable α] [LawfulOpenUpperBound α]
    [LawfulUpwardEnumerableLowerBound .closed α] [LawfulUpwardEnumerableUpperBound .open α]
    {lower : Bound .closed α} {upper : Bound .open α} :
    ((succ lower)...(succ upper)).toList =
      (lower...upper).toList.map succ :=
  toList_Rco_succ_succ_eq_map

public theorem toArray_Rco_succ_succ_eq_map [UpwardEnumerable α] [SupportsLowerBound .closed α]
    [LinearlyUpwardEnumerable α] [InfinitelyUpwardEnumerable α] [SupportsUpperBound .open α]
    [HasFiniteRanges .open α] [LawfulUpwardEnumerable α] [LawfulOpenUpperBound α]
    [LawfulUpwardEnumerableLowerBound .closed α] [LawfulUpwardEnumerableUpperBound .open α]
    {lower : Bound .closed α} {upper : Bound .open α} :
    ((succ lower)...(succ upper)).toArray =
      (lower...upper).toArray.map succ := by
  simp only [← toArray_toList]
  rw [toList_Rco_succ_succ_eq_map]
  simp only [List.map_toArray]

private theorem Internal.forIn'_eq_forIn'_iter [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α}
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    haveI := Iter.instForIn' (α := RangeIterator su α) (β := α) (n := m)
    ForIn'.forIn' r init f =
      ForIn'.forIn' (Internal.iter r) init (fun a ha acc => f a (Internal.isPlausibleIndirectOutput_iter_iff.mp ha) acc) := by
  rfl

public theorem forIn'_eq_forIn'_toList [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α}
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toList init (fun a ha acc => f a (mem_toList_iff_mem.mp ha) acc) := by
  simp [Internal.forIn'_eq_forIn'_iter, Internal.toList_eq_toList_iter,
    Iter.forIn'_eq_forIn'_toList]

public theorem forIn'_eq_forIn'_toArray [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α}
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toArray init (fun a ha acc => f a (mem_toArray_iff_mem.mp ha) acc) := by
  simp [Internal.forIn'_eq_forIn'_iter, Internal.toArray_eq_toArray_iter,
    Iter.forIn'_eq_forIn'_toArray]

public theorem forIn'_toList_eq_forIn' [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α}
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toList init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toList_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toList]

public theorem forIn'_toArray_eq_forIn' [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α}
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toArray init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toArray_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toArray]

public theorem mem_of_mem_open [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    [SupportsLowerBound .open α] [LawfulUpwardEnumerableLowerBound .open α]
    {r : PRange ⟨sl, su⟩ α} {a b : α}
    (hrb : SupportsLowerBound.IsSatisfied r.lower b)
    (hmem : a ∈ PRange.mk (shape := ⟨.open, su⟩) b r.upper) :
    a ∈ r := by
  refine ⟨?_, hmem.2⟩
  have := hmem.1
  simp only [LawfulUpwardEnumerableLowerBound.isSatisfied_iff, init?] at this hrb ⊢
  obtain ⟨init, hi⟩ := hrb
  obtain ⟨b', hb'⟩ := this
  refine ⟨init, hi.1, UpwardEnumerable.le_trans hi.2 (UpwardEnumerable.le_trans ?_ hb'.2)⟩
  exact UpwardEnumerable.le_of_succ?_eq hb'.1

public theorem SupportsLowerBound.isSatisfied_init? {sl} [UpwardEnumerable α]
    [SupportsLowerBound sl α] [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α]
    {bound : Bound sl α} {a : α} (h : init? bound = some a) :
    SupportsLowerBound.IsSatisfied bound a := by
  simp only [LawfulUpwardEnumerableLowerBound.isSatisfied_iff]
  exact ⟨a, h, UpwardEnumerable.le_refl _⟩

public theorem forIn'_eq_match {sl su} [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    [SupportsLowerBound .open α] [LawfulUpwardEnumerableLowerBound .open α]
    {r : PRange ⟨sl, su⟩ α}
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f = match hi : init? r.lower with
      | none => pure init
      | some a => if hu : SupportsUpperBound.IsSatisfied r.upper a then do
        match ← f a ⟨SupportsLowerBound.isSatisfied_init? hi, hu⟩ init with
        | .yield c =>
          ForIn'.forIn' (α := α) (β := γ) (PRange.mk (shape := ⟨.open, su⟩) a r.upper) c
            (fun a ha acc => f a (mem_of_mem_open (SupportsLowerBound.isSatisfied_init? hi) ha) acc)
        | .done c => return c
      else
        return init := by
  rw [Internal.forIn'_eq_forIn'_iter, Iter.forIn'_eq_match_step]
  simp only [RangeIterator.step_eq_step, RangeIterator.step, Internal.iter]
  apply Eq.symm
  split <;> rename_i heq
  · simp [heq]
  · simp only [heq]
    split
    · simp only
      apply bind_congr
      intro step
      split
      · simp [Internal.forIn'_eq_forIn'_iter, Internal.iter, BoundedUpwardEnumerable.init?]
      · simp
    · simp

public instance {su} [UpwardEnumerable α] [SupportsUpperBound su α] [RangeSize su α]
    [LawfulUpwardEnumerable α] [HasFiniteRanges su α] [LawfulRangeSize su α] :
    LawfulIteratorSize (RangeIterator su α) where
  size_eq_size_toArray {it} := by
    simp only [Iter.size, IteratorSize.size, Iter.toIterM]
    split <;> rename_i heq
    · rw [Iter.toArray_eq_match_step, RangeIterator.step_eq_step]
      simp [RangeIterator.step, heq]
    · rename_i next
      simp only [Id.run_pure]
      induction h : RangeSize.size it.internalState.upperBound _ generalizing it next
      · rw [Iter.toArray_eq_match_step, RangeIterator.step_eq_step]
        simp only [RangeIterator.step, heq]
        by_cases h : SupportsUpperBound.IsSatisfied it.internalState.upperBound next
        · exfalso
          cases hn : UpwardEnumerable.succ? next
          · have := LawfulRangeSize.size_eq_one_of_succ?_eq_none _ _ h hn
            simp [*] at this
          · have := LawfulRangeSize.size_eq_succ_of_succ?_eq_some _ _ _ h hn
            simp [*] at this
        · simp [h]
      · rename_i ih
        by_cases h' : SupportsUpperBound.IsSatisfied it.internalState.upperBound next
        · rw [Iter.toArray_eq_match_step, RangeIterator.step_eq_step]
          simp only [RangeIterator.step, heq, h', ↓reduceIte, Array.size_append, List.size_toArray,
            List.length_cons, List.length_nil, Nat.zero_add]
          cases hn : UpwardEnumerable.succ? next
          · rw [Iter.toArray_eq_match_step, RangeIterator.step_eq_step]
            simp only [RangeIterator.step, Array.size_empty]
            simp_all [LawfulRangeSize.size_eq_one_of_succ?_eq_none _ _ h' hn]
          · rename_i next'
            have := LawfulRangeSize.size_eq_succ_of_succ?_eq_some _ _ _ h' hn
            simp only [this, Nat.add_right_cancel_iff] at h
            specialize ih (it := ⟨⟨some next', it.internalState.upperBound⟩⟩) next' rfl h
            rw [ih, Nat.add_comm]
        · have := LawfulRangeSize.size_eq_zero_of_not_isSatisfied _ _ h'
          simp [*] at this

public theorem length_toList {sl su} [UpwardEnumerable α] [SupportsUpperBound su α]
    [RangeSize su α] [LawfulUpwardEnumerable α] [BoundedUpwardEnumerable sl α]
    [HasFiniteRanges su α] [LawfulRangeSize su α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList.length = r.size := by
  simp [PRange.toList, PRange.size]

public theorem size_toArray {sl su} [UpwardEnumerable α] [SupportsUpperBound su α]
    [RangeSize su α] [LawfulUpwardEnumerable α] [BoundedUpwardEnumerable sl α]
    [HasFiniteRanges su α] [LawfulRangeSize su α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toArray.size = r.size := by
  simp [PRange.toArray, PRange.size]

public theorem isEmpty_iff_forall_not_mem {sl su} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [BoundedUpwardEnumerable sl α] [SupportsLowerBound sl α] [SupportsUpperBound su α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α} :
    r.isEmpty ↔ ∀ a, ¬ a ∈ r := by
  simp only [PRange.isEmpty, Option.all_eq_true_iff_get]
  constructor
  · intro h a hmem
    have hl := hmem.1
    have hu := hmem.2
    simp only [LawfulUpwardEnumerableLowerBound.isSatisfied_iff] at hl
    obtain ⟨init, hi, hl⟩ := hl
    have : SupportsUpperBound.IsSatisfied r.upper init :=
      LawfulUpwardEnumerableUpperBound.isSatisfied_of_le r.upper _ a hu hl
    simp only [Option.eq_some_iff_get_eq] at hi
    specialize h hi.choose
    simp [hi.choose_spec, this] at h
  · intro h hi
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    intro hu
    have hl := SupportsLowerBound.isSatisfied_init? (bound := r.lower)
      (Option.some_get hi).symm
    exact h ((init? r.lower).get hi) ⟨hl, hu⟩

theorem Std.PRange.getElem?_toList_Rcx_eq [LE α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [SupportsUpperBound su α] [LawfulUpwardEnumerableUpperBound su α]
    [LawfulUpwardEnumerableLE α] [HasFiniteRanges su α]
    {r : PRange ⟨.closed, su⟩ α} {i} :
    r.toList[i]? = (UpwardEnumerable.succMany? i r.lower).filter (SupportsUpperBound.IsSatisfied r.upper) := by
  induction i generalizing r
  · rw [PRange.toList_eq_match, UpwardEnumerable.succMany?_zero]
    simp only [Option.filter_some, decide_eq_true_eq]
    split <;> simp
  · rename_i n ih
    rw [PRange.toList_eq_match]
    simp only
    split
    · simp [UpwardEnumerable.succMany?_succ?_eq_succ?_bind_succMany?]
      cases hs : UpwardEnumerable.succ? r.lower
      · rw [PRange.toList_eq_match]
        simp [BoundedUpwardEnumerable.init?, hs]
      · rw [toList_Rox_eq_toList_Rcx_of_isSome_succ? (by simp [hs])]
        rw [ih]
        simp [hs]
    · simp only [List.length_nil, Nat.not_lt_zero, not_false_eq_true, getElem?_neg]
      cases hs : UpwardEnumerable.succMany? (n + 1) r.lower
      · simp
      · rename_i hl a
        simp only [Option.filter_some, decide_eq_true_eq, right_eq_ite_iff]
        have : UpwardEnumerable.LE r.lower a := ⟨n + 1, hs⟩
        intro ha
        exact hl.elim <| LawfulUpwardEnumerableUpperBound.isSatisfied_of_le r.upper _ _ ha this (α := α)

theorem Std.PRange.getElem?_toArray_Rcx_eq [LE α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [SupportsUpperBound su α] [LawfulUpwardEnumerableUpperBound su α]
    [LawfulUpwardEnumerableLE α] [HasFiniteRanges su α]
    {r : PRange ⟨.closed, su⟩ α} {i} :
    r.toArray[i]? = (UpwardEnumerable.succMany? i r.lower).filter (SupportsUpperBound.IsSatisfied r.upper) := by
  rw [← toArray_toList, List.getElem?_toArray, getElem?_toList_Rcx_eq]

theorem Std.PRange.isSome_succMany?_of_lt_length_toList_Rcx [LE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [SupportsUpperBound su α] [LawfulUpwardEnumerableUpperBound su α]
    [LawfulUpwardEnumerableLE α] [HasFiniteRanges su α]
    {r : PRange ⟨.closed, su⟩ α} {i} (h : i < r.toList.length) :
    (UpwardEnumerable.succMany? i r.lower).isSome := by
  have : r.toList[i]?.isSome := by simp [h]
  simp only [getElem?_toList_Rcx_eq, Option.isSome_filter] at this
  exact Option.isSome_of_any this

theorem Std.PRange.isSome_succMany?_of_lt_size_toArray_Rcx [LE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [SupportsUpperBound su α] [LawfulUpwardEnumerableUpperBound su α]
    [LawfulUpwardEnumerableLE α] [HasFiniteRanges su α]
    {r : PRange ⟨.closed, su⟩ α} {i} (h : i < r.toArray.size) :
    (UpwardEnumerable.succMany? i r.lower).isSome := by
  have : r.toArray[i]?.isSome := by simp [h]
  simp only [getElem?_toArray_Rcx_eq, Option.isSome_filter] at this
  exact Option.isSome_of_any this

theorem Std.PRange.getElem_toList_Rcx_eq [LE α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [SupportsUpperBound su α] [LawfulUpwardEnumerableUpperBound su α]
    [LawfulUpwardEnumerableLE α] [HasFiniteRanges su α]
    {r : PRange ⟨.closed, su⟩ α} {i h} :
    r.toList[i]'h = (UpwardEnumerable.succMany? i r.lower).get
        (isSome_succMany?_of_lt_length_toList_Rcx h) := by
  simp [List.getElem_eq_getElem?_get, getElem?_toList_Rcx_eq]

theorem Std.PRange.getElem_toArray_Rcx_eq [LE α] [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [SupportsUpperBound su α] [LawfulUpwardEnumerableUpperBound su α]
    [LawfulUpwardEnumerableLE α] [HasFiniteRanges su α]
    {r : PRange ⟨.closed, su⟩ α} {i h} :
    r.toArray[i]'h = (UpwardEnumerable.succMany? i r.lower).get
        (isSome_succMany?_of_lt_size_toArray_Rcx h) := by
  simp [Array.getElem_eq_getElem?_get, getElem?_toArray_Rcx_eq]

theorem Std.PRange.eq_succMany?_of_toList_Rcx_eq_append_cons [LE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [SupportsUpperBound su α] [HasFiniteRanges su α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨.closed, su⟩ α} {pref suff : List α} {cur : α} (h : r.toList = pref ++ cur :: suff) :
    cur = (UpwardEnumerable.succMany? pref.length r.lower).get
        (isSome_succMany?_of_lt_length_toList_Rcx (by simp [h])) := by
  have : cur = (pref ++ cur :: suff)[pref.length] := by simp
  simp only [← h] at this
  simp [this, getElem_toList_Rcx_eq]

theorem Std.PRange.eq_succMany?_of_toArray_Rcx_eq_append_append [LE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [SupportsUpperBound su α] [HasFiniteRanges su α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨.closed, su⟩ α} {pref suff : Array α} {cur : α} (h : r.toArray = pref ++ #[cur] ++ suff) :
    cur = (UpwardEnumerable.succMany? pref.size r.lower).get
        (isSome_succMany?_of_lt_size_toArray_Rcx (by simp [h, Nat.add_assoc, Nat.add_comm 1])) := by
  have : cur = (pref ++ #[cur] ++ suff)[pref.size] := by simp
  simp only [← h] at this
  simp [this, getElem_toArray_Rcx_eq]

end Std.PRange
