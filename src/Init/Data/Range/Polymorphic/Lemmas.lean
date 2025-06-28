/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators
public import Init.Data.Iterators.Lemmas.Consumers.Collect
public import all Init.Data.Range.Polymorphic.Basic
public import all Init.Data.Range.Polymorphic.RangeIterator
public import all Init.Data.Range.Polymorphic.Iterators
public import all Init.Data.Iterators.Consumers.Loop

public section

/-!
# Lemmas about ranges

This file provides lemmas about `Std.PRange`.
-/

namespace Std.PRange
open Std.Iterators

variable {shape : RangeShape} {α : Type u}

private theorem Internal.iter_open_eq_iter_closed_of_isSome_succ? {su} [UpwardEnumerable α]
    [SupportsUpperBound su α] [HasFiniteRanges su α]
    [LawfulUpwardEnumerable α]
    {lo : Bound .open α} {hi} (h : (UpwardEnumerable.succ? lo).isSome) :
    Internal.iter (PRange.mk (shape := ⟨.open, su⟩) lo hi) =
      Internal.iter (PRange.mk (shape := ⟨.closed, su⟩) (UpwardEnumerable.succ? lo |>.get h) hi) := by
  simp [Internal.iter, BoundedUpwardEnumerable.init?]

private theorem Internal.toList_eq_toList_iter {sl su} [UpwardEnumerable α]
    [BoundedUpwardEnumerable sl α] [SupportsUpperBound su α] [HasFiniteRanges su α]
    [LawfulUpwardEnumerable α] {r : PRange ⟨sl, su⟩ α} :
    r.toList = (Internal.iter r).toList := by
  rfl

theorem RangeIterator.toList_eq_match {su} [UpwardEnumerable α]
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

theorem toList_eq_match {sl su} [UpwardEnumerable α] [BoundedUpwardEnumerable sl α]
    [SupportsUpperBound su α] [HasFiniteRanges su α]
    [LawfulUpwardEnumerable α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList = match BoundedUpwardEnumerable.init? r.lower with
      | none => []
      | some a => if SupportsUpperBound.IsSatisfied r.upper a then
        a :: (PRange.mk (shape := ⟨.open, su⟩) a r.upper).toList
      else
        [] := by
  rw [Internal.toList_eq_toList_iter, RangeIterator.toList_eq_match]; rfl

theorem toList_open_eq_toList_closed_of_isSome_succ? {su} [UpwardEnumerable α]
    [SupportsUpperBound su α] [HasFiniteRanges su α]
    [LawfulUpwardEnumerable α]
    {lo : Bound .open α} {hi} (h : (UpwardEnumerable.succ? lo).isSome) :
    (PRange.mk (shape := ⟨.open, su⟩) lo hi).toList =
      (PRange.mk (shape := ⟨.closed, su⟩) (UpwardEnumerable.succ? lo |>.get h) hi).toList := by
  simp [Internal.toList_eq_toList_iter, Internal.iter_open_eq_iter_closed_of_isSome_succ?, h]

theorem toList_eq_nil_iff {sl su} [UpwardEnumerable α]
    [SupportsUpperBound su α] [HasFiniteRanges su α] [BoundedUpwardEnumerable sl α]
    [LawfulUpwardEnumerable α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList = [] ↔
      ¬ (∃ a, BoundedUpwardEnumerable.init? r.lower = some a ∧ SupportsUpperBound.IsSatisfied r.upper a) := by
  rw [Internal.toList_eq_toList_iter]
  rw [RangeIterator.toList_eq_match, Internal.iter]
  simp only
  split <;> rename_i heq <;> simp [heq]

theorem mem_toList_iff_mem {sl su} [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α}
    {a : α} : a ∈ r.toList ↔ a ∈ r := by
  rw [Internal.toList_eq_toList_iter, Iter.mem_toList_iff_isPlausibleIndirectOutput,
    Internal.isPlausibleIndirectOutput_iter_iff]

theorem BoundedUpwardEnumerable.Closed.init?_succ [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] {lower lower' : Bound .closed α}
    (h : UpwardEnumerable.succ? lower = some lower') :
    BoundedUpwardEnumerable.init? lower' = (BoundedUpwardEnumerable.init? lower).bind UpwardEnumerable.succ? := by
  cases h : init? lower <;> rename_i ilower <;> cases h' : init? lower' <;> rename_i ilower'
  · simp
  · simp [init?] at h
  · simp [init?] at h'
  · simp_all [init?]

theorem pairwise_toList_upwardEnumerableLt {sl su} [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList.Pairwise (fun a b => UpwardEnumerable.LT a b) := by
  rw [Internal.toList_eq_toList_iter]
  generalize Internal.iter r = it
  induction it using Iter.inductSteps with | step it ihy ihs =>
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
      simp only [UpwardEnumerable.succMany?_succ, UpwardEnumerable.succMany?_zero,
        Option.bind_some]
      exact ha.choose_spec.1
    exact UpwardEnumerable.lt_of_lt_of_le this ha.choose_spec.2
  · apply ihy (out := a)
    simp_all [RangeIterator.isPlausibleStep_iff, RangeIterator.step]

theorem pairwise_toList_ne {sl su} [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList.Pairwise (fun a b => a ≠ b) :=
  List.Pairwise.imp (fun hlt => UpwardEnumerable.ne_of_lt hlt) pairwise_toList_upwardEnumerableLt

theorem pairwise_toList_lt {sl su} [LT α] [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList.Pairwise (fun a b => a < b) :=
  List.Pairwise.imp
    (fun hlt => (LawfulUpwardEnumerableLT.lt_iff ..).mpr hlt) pairwise_toList_upwardEnumerableLt

theorem pairwise_toList_le {sl su} [LE α] [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α} :
    r.toList.Pairwise (fun a b => a ≤ b) :=
  pairwise_toList_upwardEnumerableLt
    |> List.Pairwise.imp UpwardEnumerable.le_of_lt
    |> List.Pairwise.imp (fun hle => (LawfulUpwardEnumerableLE.le_iff ..).mpr hle)

theorem ClosedOpen.mem_succ_iff [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [InfinitelyUpwardEnumerable α] [SupportsUpperBound .open α]
    [SupportsLowerBound .closed α] [LawfulUpwardEnumerableLowerBound .closed α]
    [HasFiniteRanges .open α] [LawfulUpwardEnumerable α] [LawfulOpenUpperBound α]
    {lower : Bound .closed α} {upper : Bound .open α} {a : α} :
    a ∈ PRange.mk (shape := ⟨.closed, .open⟩) (UpwardEnumerable.succ lower) (UpwardEnumerable.succ upper) ↔
      ∃ a', a = UpwardEnumerable.succ a' ∧ a' ∈ PRange.mk (shape := ⟨.closed, .open⟩) lower upper := by
  simp [Membership.mem, LawfulUpwardEnumerableLowerBound.isSatisfied_iff,
    BoundedUpwardEnumerable.init?, LawfulOpenUpperBound.isSatisfied_iff_le]
  rw [← Option.some_get (InfinitelyUpwardEnumerable.isSome_succ? _)]
  simp only [Option.some.injEq, ← UpwardEnumerable.succ.eq_def]
  simp
  constructor
  · rintro ⟨⟨n, hn⟩, h⟩
    rw [UpwardEnumerable.succMany?_eq_some_iff_succMany, ← UpwardEnumerable.succMany_one,
      ← UpwardEnumerable.succMany_add, Nat.add_comm, UpwardEnumerable.succMany_add,
      UpwardEnumerable.succMany_one] at hn
    rw [← hn]
    refine ⟨UpwardEnumerable.succMany n lower, rfl, ?_, ?_⟩
    · exact ⟨n, by simp [UpwardEnumerable.succMany_eq_get]⟩
    · obtain ⟨m, hm⟩ := h
      refine ⟨m, ?_⟩
      rw [UpwardEnumerable.succMany?_eq_some_iff_succMany] at hm ⊢
      rwa [← hn, ← UpwardEnumerable.succMany_one, ← UpwardEnumerable.succMany_add, Nat.add_comm,
        UpwardEnumerable.succMany_add, UpwardEnumerable.succMany_one,
        UpwardEnumerable.succ_eq_succ_iff] at hm
  · rintro ⟨a', rfl, hl, hu⟩
    simp [UpwardEnumerable.succ_le_succ_iff, UpwardEnumerable.succ_lt_succ_iff]
    exact ⟨hl, hu⟩

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

theorem ClosedOpen.toList_succ_succ_eq_map [UpwardEnumerable α] [SupportsLowerBound .closed α]
    [LinearlyUpwardEnumerable α] [InfinitelyUpwardEnumerable α] [SupportsUpperBound .open α]
    [HasFiniteRanges .open α] [LawfulUpwardEnumerable α] [LawfulOpenUpperBound α]
    [LawfulUpwardEnumerableLowerBound .closed α] [LawfulUpwardEnumerableUpperBound .open α]
    {lower : Bound .closed α} {upper : Bound .open α} :
    (PRange.mk (shape := ⟨.closed, .open⟩) (UpwardEnumerable.succ lower) (UpwardEnumerable.succ upper)).toList =
      (PRange.mk (shape := ⟨.closed, .open⟩) lower upper).toList.map UpwardEnumerable.succ := by
  apply eq_of_pairwise_lt_of_mem_iff_mem (lt := UpwardEnumerable.LT) (asymm := ?_)
  · apply pairwise_toList_upwardEnumerableLt
  · apply List.Pairwise.map (R := UpwardEnumerable.LT) (S := UpwardEnumerable.LT)
    · intro a b
      exact UpwardEnumerable.succ_lt_succ_iff.mpr
    · apply pairwise_toList_upwardEnumerableLt
  · simp only [List.mem_map, mem_toList_iff_mem]
    intro a
    rw [mem_succ_iff]
    constructor
    · rintro ⟨a, rfl, h⟩
      exact ⟨a, h, rfl⟩
    · rintro ⟨a, h, h'⟩
      exact ⟨_, h'.symm, h⟩
  · exact ⟨fun _ _ => UpwardEnumerable.not_gt_of_lt⟩

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

theorem forIn'_eq_forIn'_toList [UpwardEnumerable α]
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

theorem forIn'_toList_eq_forIn' [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    {r : PRange ⟨sl, su⟩ α}
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toList init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toList_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toList]

theorem mem_of_mem_open [UpwardEnumerable α]
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
  simp only [LawfulUpwardEnumerableLowerBound.isSatisfied_iff,
    BoundedUpwardEnumerable.init?] at this hrb ⊢
  obtain ⟨init, hi⟩ := hrb
  obtain ⟨b', hb'⟩ := this
  refine ⟨init, hi.1, UpwardEnumerable.le_trans hi.2 (UpwardEnumerable.le_trans ?_ hb'.2)⟩
  exact UpwardEnumerable.le_of_succ?_eq hb'.1

theorem SupportsLowerBound.isSatisfied_init? {sl} [UpwardEnumerable α]
    [SupportsLowerBound sl α] [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α]
    {bound : Bound sl α} {a : α} (h : BoundedUpwardEnumerable.init? bound = some a) :
    SupportsLowerBound.IsSatisfied bound a := by
  simp only [LawfulUpwardEnumerableLowerBound.isSatisfied_iff]
  exact ⟨a, h, UpwardEnumerable.le_refl _⟩

theorem forIn'_eq_match {sl su} [UpwardEnumerable α]
    [SupportsUpperBound su α] [SupportsLowerBound sl α] [HasFiniteRanges su α]
    [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLowerBound sl α] [LawfulUpwardEnumerableUpperBound su α]
    [SupportsLowerBound .open α] [LawfulUpwardEnumerableLowerBound .open α]
    {r : PRange ⟨sl, su⟩ α}
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f = match hi : BoundedUpwardEnumerable.init? r.lower with
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

instance {su} [UpwardEnumerable α] [SupportsUpperBound su α] [RangeSize su α]
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
          · have := LawfulRangeSize.size_eq_succ_of_succ?_eq_some _ _ h hn
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
            have := LawfulRangeSize.size_eq_succ_of_succ?_eq_some _ _ h' hn
            simp only [this, Nat.add_right_cancel_iff] at h
            specialize ih (it := ⟨⟨some next', it.internalState.upperBound⟩⟩) next' rfl h
            rw [ih, Nat.add_comm]
        · have := LawfulRangeSize.size_eq_zero_of_not_satisfied _ _ h'
          simp [*] at this

theorem isEmpty_iff_forall_not_mem {sl su} [UpwardEnumerable α] [LawfulUpwardEnumerable α]
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
    exact h ((BoundedUpwardEnumerable.init? r.lower).get hi) ⟨hl, hu⟩

end Std.PRange
