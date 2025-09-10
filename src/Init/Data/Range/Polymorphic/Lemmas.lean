/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Lemmas.Consumers.Loop
import Init.Data.Iterators.Lemmas.Consumers.Collect
public import Init.Data.Range.Polymorphic.Basic
import all Init.Data.Range.Polymorphic.Basic
public import Init.Data.Range.Polymorphic.RangeIterator
import all Init.Data.Range.Polymorphic.RangeIterator
public import Init.Data.Range.Polymorphic.Iterators
import all Init.Data.Range.Polymorphic.Iterators
public import Init.Data.Iterators.Consumers.Loop
import all Init.Data.Iterators.Consumers.Loop

public section

/-!
# Lemmas about ranges

This file provides lemmas about `Std.PRange`.
-/

namespace Std
open Std.PRange Std.Iterators

variable {α : Type u}

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

theorem PRange.UpwardEnumerable.exists_of_succ_le [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [InfinitelyUpwardEnumerable α]
    {a b : α} (h : UpwardEnumerable.LE (succ a) b) :
    ∃ b', b = succ b' ∧ UpwardEnumerable.LE a b' := by
  obtain ⟨n, hn⟩ := h
  rw [succMany?_eq_some_iff_succMany, succMany_succ_eq_succ_succMany] at hn
  exact ⟨succMany n a, hn.symm, ⟨n, succMany?_eq_some⟩⟩

private theorem Rcc.Internal.forIn'_eq_forIn'_iter [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] {r : Rcc α}
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    haveI := Iter.instForIn' (α := Rxc.Iterator α) (β := α) (n := m)
    ForIn'.forIn' r init f =
      ForIn'.forIn' (Internal.iter r) init (fun a ha acc => f a (Internal.isPlausibleIndirectOutput_iter_iff.mp ha) acc) := by
  rfl

private theorem Rcc.Internal.toList_eq_toList_iter [LE α] [DecidableLE α]
    [UpwardEnumerable α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] {r : Rcc α} :
    r.toList = (Internal.iter r).toList := by
  rfl

private theorem Rco.Internal.forIn'_eq_forIn'_iter [LE α] [DecidableLE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] {r : Rco α}
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    haveI := Iter.instForIn' (α := Rxo.Iterator α) (β := α) (n := m)
    ForIn'.forIn' r init f =
      ForIn'.forIn' (Internal.iter r) init (fun a ha acc => f a (Internal.isPlausibleIndirectOutput_iter_iff.mp ha) acc) := by
  rfl

private theorem Rco.Internal.toList_eq_toList_iter [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] {r : Rco α} :
    r.toList = (Internal.iter r).toList := by
  rfl

private theorem Rci.Internal.forIn'_eq_forIn'_iter [LE α] [DecidableLE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] {r : Rci α}
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    haveI := Iter.instForIn' (α := Rxi.Iterator α) (β := α) (n := m)
    ForIn'.forIn' r init f =
      ForIn'.forIn' (Internal.iter r) init (fun a ha acc => f a (Internal.isPlausibleIndirectOutput_iter_iff.mp ha) acc) := by
  rfl

private theorem Rci.Internal.toList_eq_toList_iter [LE α]
    [UpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Rci α} :
    r.toList = (Internal.iter r).toList := by
  rfl

private theorem Roc.Internal.forIn'_eq_forIn'_iter [LE α] [DecidableLE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] {r : Roc α}
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    haveI := Iter.instForIn' (α := Rxc.Iterator α) (β := α) (n := m)
    ForIn'.forIn' r init f =
      ForIn'.forIn' (Internal.iter r) init (fun a ha acc => f a (Internal.isPlausibleIndirectOutput_iter_iff.mp ha) acc) := by
  rfl

private theorem Roc.Internal.toList_eq_toList_iter [LE α] [DecidableLE α]
    [UpwardEnumerable α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] {r : Roc α} :
    r.toList = (Internal.iter r).toList := by
  rfl

private theorem Roo.Internal.forIn'_eq_forIn'_iter [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] {r : Roo α}
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    haveI := Iter.instForIn' (α := Rxo.Iterator α) (β := α) (n := m)
    ForIn'.forIn' r init f =
      ForIn'.forIn' (Internal.iter r) init (fun a ha acc => f a (Internal.isPlausibleIndirectOutput_iter_iff.mp ha) acc) := by
  rfl

private theorem Roo.Internal.toList_eq_toList_iter [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] {r : Roo α} :
    r.toList = (Internal.iter r).toList := by
  rfl

private theorem Roi.Internal.forIn'_eq_forIn'_iter [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] {r : Roi α}
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    haveI := Iter.instForIn' (α := Rxi.Iterator α) (β := α) (n := m)
    ForIn'.forIn' r init f =
      ForIn'.forIn' (Internal.iter r) init (fun a ha acc => f a (Internal.isPlausibleIndirectOutput_iter_iff.mp ha) acc) := by
  rfl

private theorem Roi.Internal.toList_eq_toList_iter [LE α]
    [UpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {r : Roi α} :
    r.toList = (Internal.iter r).toList := by
  rfl

public theorem Rxc.Iterator.toList_eq_match [LE α] [DecidableLE α]
    [UpwardEnumerable α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLE α]
    {it : Iter (α := Rxc.Iterator α) α} :
    it.toList =  match it.internalState.next with
      | none => []
      | some a => if a ≤ it.internalState.upperBound then
          a :: (⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩ : Iter (α := Rxc.Iterator α) α).toList
        else
          [] := by
  apply Eq.symm
  rw [Iter.toList_eq_match_step, Rxc.Iterator.step_eq_step]
  simp only [Rxc.Iterator.step]
  split <;> rename_i heq
  · simp [*]
  · split <;> rename_i heq' <;> simp [*]

public theorem Rxo.Iterator.toList_eq_match [LT α] [DecidableLT α]
    [UpwardEnumerable α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α]
    {it : Iter (α := Rxo.Iterator α) α} :
    it.toList =  match it.internalState.next with
      | none => []
      | some a => if a < it.internalState.upperBound then
          a :: (⟨⟨UpwardEnumerable.succ? a, it.internalState.upperBound⟩⟩ : Iter (α := Rxo.Iterator α) α).toList
        else
          [] := by
  apply Eq.symm
  simp only [Iter.toList_eq_match_step (it := it), Rxo.Iterator.step_eq_step, Rxo.Iterator.step]
  split <;> rename_i heq
  · simp [*]
  · split <;> rename_i heq' <;> simp [*]

public theorem Rxi.Iterator.toList_eq_match
    [UpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {it : Iter (α := Rxi.Iterator α) α} :
    it.toList =  match it.internalState.next with
      | none => []
      | some a =>
          a :: (⟨⟨UpwardEnumerable.succ? a⟩⟩ : Iter (α := Rxi.Iterator α) α).toList := by
  apply Eq.symm
  simp only [Iter.toList_eq_match_step (it := it), Rxi.Iterator.step_eq_step, Rxi.Iterator.step]
  split <;> rename_i heq <;> simp [*]

public theorem Rxc.Iterator.pairwise_toList_upwardEnumerableLt [LE α] [DecidableLE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    (it : Iter (α := Rxc.Iterator α) α) :
    it.toList.Pairwise (fun a b => UpwardEnumerable.LT a b) := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [Rxc.Iterator.toList_eq_match]
  repeat' split <;> (try exact .nil; done)
  rename_i a _ _
  apply List.Pairwise.cons
  · intro a' ha
    rw [Iter.mem_toList_iff_isPlausibleIndirectOutput] at ha
    replace ha := Rxc.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput ha
    simp only at ha
    have : UpwardEnumerable.LT a ha.choose := by
      refine ⟨0, ?_⟩
      simp only [succMany?_succ?, succMany?_zero,
        Option.bind_some]
      exact ha.choose_spec.1
    exact UpwardEnumerable.lt_of_lt_of_le this ha.choose_spec.2
  · apply ihy (out := a)
    simp_all [Rxc.Iterator.isPlausibleStep_iff, Rxc.Iterator.step]

public theorem Rxo.Iterator.pairwise_toList_upwardEnumerableLt [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    (it : Iter (α := Rxo.Iterator α) α) :
    it.toList.Pairwise (fun a b => UpwardEnumerable.LT a b) := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [Rxo.Iterator.toList_eq_match]
  repeat' split <;> (try exact .nil; done)
  rename_i a _ _
  apply List.Pairwise.cons
  · intro a' ha
    rw [Iter.mem_toList_iff_isPlausibleIndirectOutput] at ha
    replace ha := Rxo.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput ha
    simp only at ha
    have : UpwardEnumerable.LT a ha.choose := by
      refine ⟨0, ?_⟩
      simp only [succMany?_succ?, succMany?_zero,
        Option.bind_some]
      exact ha.choose_spec.1
    exact UpwardEnumerable.lt_of_lt_of_le this ha.choose_spec.2
  · apply ihy (out := a)
    simp_all [Rxo.Iterator.isPlausibleStep_iff, Rxo.Iterator.step]

public theorem Rxi.Iterator.pairwise_toList_upwardEnumerableLt
    [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    (it : Iter (α := Rxi.Iterator α) α) :
    it.toList.Pairwise (fun a b => UpwardEnumerable.LT a b) := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [Rxi.Iterator.toList_eq_match]
  repeat' split <;> (try exact .nil; done)
  rename_i a _
  apply List.Pairwise.cons
  · intro a' ha
    rw [Iter.mem_toList_iff_isPlausibleIndirectOutput] at ha
    replace ha := Rxi.Iterator.upwardEnumerableLe_of_isPlausibleIndirectOutput ha
    simp only at ha
    have : UpwardEnumerable.LT a ha.choose := by
      refine ⟨0, ?_⟩
      simp only [succMany?_succ?, succMany?_zero,
        Option.bind_some]
      exact ha.choose_spec.1
    exact UpwardEnumerable.lt_of_lt_of_le this ha.choose_spec.2
  · apply ihy (out := a)
    simp_all [Rxi.Iterator.isPlausibleStep_iff, Rxi.Iterator.step]

public instance [LE α] [DecidableLE α] [UpwardEnumerable α] [Rxc.HasSize α] [Rxc.LawfulHasSize α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    LawfulIteratorSize (Rxc.Iterator α) where
  size_eq_size_toArray {it} := by
    simp only [Iter.size, IteratorSize.size, Iter.toIterM]
    split <;> rename_i heq
    · simp [Iter.toArray_eq_match_step (it := it), Rxc.Iterator.step_eq_step, Rxc.Iterator.step, heq]
    · rename_i next
      simp only [Id.run_pure]
      induction h : Rxc.HasSize.size _ it.internalState.upperBound generalizing it next
      · simp only [Rxc.size_eq_zero_iff_not_le] at h
        simp [Iter.toArray_eq_match_step (it := it), Rxc.Iterator.step_eq_step, Rxc.Iterator.step, heq, h]
      · rename_i ih
        have h' : next ≤ it.internalState.upperBound := Rxc.size_pos_iff_isSatisfied.mp (by omega)
        simp only [Iter.toArray_eq_match_step (it := it), Rxc.Iterator.step_eq_step,
            Rxc.Iterator.step, heq, h', ↓reduceIte]
        cases hn : UpwardEnumerable.succ? next
        · rw [Iter.toArray_eq_match_step, Rxc.Iterator.step_eq_step]
          simp_all [Rxc.Iterator.step, Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none _ _ h' hn]
        · have := Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ _ h' hn
          simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
            Nat.zero_add]
          rw [← ih _ rfl] <;> (try simp) <;> omega

public instance [LT α] [DecidableLT α] [UpwardEnumerable α] [Rxo.HasSize α]
    [Rxo.LawfulHasSize α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    LawfulIteratorSize (Rxo.Iterator α) where
  size_eq_size_toArray {it} := by
    simp only [Iter.size, IteratorSize.size, Iter.toIterM]
    split <;> rename_i heq
    · simp [Iter.toArray_eq_match_step (it := it), Rxo.Iterator.step_eq_step, Rxo.Iterator.step, heq]
    · rename_i next
      simp only [Id.run_pure]
      induction h : Rxo.HasSize.size _ it.internalState.upperBound generalizing it next
      · simp only [Rxo.size_eq_zero_iff_not_le] at h
        simp [Iter.toArray_eq_match_step (it := it), Rxo.Iterator.step_eq_step, Rxo.Iterator.step, heq, h]
      · rename_i ih
        have h' : next < it.internalState.upperBound := Rxo.size_pos_iff_isSatisfied.mp (by omega)
        simp only [Iter.toArray_eq_match_step (it := it), Rxo.Iterator.step_eq_step,
            Rxo.Iterator.step, heq, h', ↓reduceIte]
        cases hn : UpwardEnumerable.succ? next
        · rw [Iter.toArray_eq_match_step, Rxo.Iterator.step_eq_step]
          simp_all [Rxo.Iterator.step, Rxo.LawfulHasSize.size_eq_one_of_succ?_eq_none _ _ h' hn]
        · have := Rxo.LawfulHasSize.size_eq_succ_of_succ?_eq_some _ _ _ h' hn
          simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
            Nat.zero_add]
          rw [← ih _ rfl] <;> (try simp) <;> omega

namespace Rcc

variable {r : Rcc α}

public theorem toList_eq_match [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.toList = if r.lower ≤ r.upper then
        r.lower :: (r.lower<...=r.upper).toList
      else
        [] := by
  rw [Internal.toList_eq_toList_iter, Rxc.Iterator.toList_eq_match]; rfl

public theorem toList_eq_nil_iff [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.toList = [] ↔ ¬ (r.lower ≤ r.upper) := by
  rw [Internal.toList_eq_toList_iter, Rxc.Iterator.toList_eq_match, Internal.iter]
  simp only
  split <;> rename_i heq <;> simp [heq]

public theorem mem_toList_iff_mem [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {a : α} : a ∈ r.toList ↔ a ∈ r := by
  rw [Internal.toList_eq_toList_iter, Iter.mem_toList_iff_isPlausibleIndirectOutput,
    Internal.isPlausibleIndirectOutput_iter_iff]

-- public theorem BoundedUpwardEnumerable.init?_succ?_closed [UpwardEnumerable α]
--     [LawfulUpwardEnumerable α] {lower lower' : Bound .closed α}
--     (h : UpwardEnumerable.succ? lower = some lower') :
--     init? lower' = (init? lower).bind UpwardEnumerable.succ? := by
--   cases h : init? lower <;> rename_i ilower <;> cases h' : init? lower' <;> rename_i ilower'
--   · simp
--   · simp [init?] at h
--   · simp [init?] at h'
--   · simp_all [init?]

-- @[deprecated BoundedUpwardEnumerable.init?_succ?_closed (since := "2025-08-22")]
-- public theorem BoundedUpwardEnumerable.Closed.init?_succ [UpwardEnumerable α]
--     [LawfulUpwardEnumerable α] {lower lower' : Bound .closed α}
--     (h : UpwardEnumerable.succ? lower = some lower') :
--     init? lower' = (init? lower).bind UpwardEnumerable.succ? :=
--   init?_succ?_closed h

public theorem pairwise_toList_upwardEnumerableLt [LE α] [DecidableLE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => UpwardEnumerable.LT a b) := by
  rw [Internal.toList_eq_toList_iter]
  apply Rxc.Iterator.pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_ne [LE α] [DecidableLE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a ≠ b) :=
  List.Pairwise.imp (fun hlt => UpwardEnumerable.ne_of_lt hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_lt [LE α] [DecidableLE α] [LT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a < b) :=
  List.Pairwise.imp
    (fun hlt => (LawfulUpwardEnumerableLT.lt_iff ..).mpr hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_le [LE α] [DecidableLE α] [LT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a ≤ b) :=
  pairwise_toList_upwardEnumerableLt
    |> List.Pairwise.imp UpwardEnumerable.le_of_lt
    |> List.Pairwise.imp (fun hle => (UpwardEnumerable.le_iff ..).mpr hle)

-- public theorem mem_Rco_succ_succ_iff [LE α] [DecidableLE α] [UpwardEnumerable α]
--     [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [InfinitelyUpwardEnumerable α]
--     [HasFiniteRanges .open α] [LawfulUpwardEnumerable α] [LawfulOpenUpperBound α]
--     {lower : Bound .closed α} {upper : Bound .open α} {a : α} :
--     (a ∈ (succ lower)...(succ upper)) ↔ ∃ a', a = succ a' ∧ a' ∈ lower...upper := by
--   simp [Membership.mem, LawfulUpwardEnumerableLowerBound.isSatisfied_iff,
--     init?, LawfulOpenUpperBound.isSatisfied_iff_le]
--   rw [← Option.some_get (InfinitelyUpwardEnumerable.isSome_succ? _)]
--   simp only [Option.some.injEq, ← UpwardEnumerable.succ.eq_def]
--   simp
--   constructor
--   · rintro ⟨⟨n, hn⟩, h⟩
--     rw [succMany?_eq_some_iff_succMany, ← succMany_one, ← succMany_add, Nat.add_comm, succMany_add,
--       succMany_one] at hn
--     rw [← hn]
--     refine ⟨succMany n lower, rfl, ?_, ?_⟩
--     · exact ⟨n, by simp [succMany_eq_get]⟩
--     · obtain ⟨m, hm⟩ := h
--       refine ⟨m, ?_⟩
--       rw [succMany?_eq_some_iff_succMany] at hm ⊢
--       rwa [← hn, ← succMany_one, ← succMany_add, Nat.add_comm, succMany_add, succMany_one,
--         succ_eq_succ_iff] at hm
--   · rintro ⟨a', rfl, hl, hu⟩
--     simp [UpwardEnumerable.succ_le_succ_iff, UpwardEnumerable.succ_lt_succ_iff]
--     exact ⟨hl, hu⟩

public theorem mem_succ_succ_iff [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [InfinitelyUpwardEnumerable α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo hi a : α} :
    (a ∈ (succ lo)...=(succ hi)) ↔ ∃ a', a = succ a' ∧ a' ∈ lo...=hi := by
  simp [Membership.mem, LawfulUpwardEnumerableLE.le_iff]
  constructor
  · intro h
    obtain ⟨a', rfl, ha'⟩ := UpwardEnumerable.exists_of_succ_le h.1
    exact ⟨a', rfl, ha', UpwardEnumerable.succ_le_succ_iff.mp h.2⟩
  · rintro ⟨a', rfl, hl, hu⟩
    simp only [UpwardEnumerable.succ_le_succ_iff]
    exact ⟨hl, hu⟩

public theorem succ_mem_succ_succ_iff [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [InfinitelyUpwardEnumerable α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo hi a : α} :
    (succ a ∈ (succ lo)...=(succ hi)) ↔ a ∈ lo...=hi := by
  simp [mem_succ_succ_iff, UpwardEnumerable.succ_inj]

-- public theorem toList_Rco_succ_succ_eq_map [UpwardEnumerable α] [SupportsLowerBound .closed α]
--     [LinearlyUpwardEnumerable α] [InfinitelyUpwardEnumerable α] [SupportsUpperBound .open α]
--     [HasFiniteRanges .open α] [LawfulUpwardEnumerable α] [LawfulOpenUpperBound α]
--     [LawfulUpwardEnumerableLowerBound .closed α] [LawfulUpwardEnumerableUpperBound .open α]
--     {lower : Bound .closed α} {upper : Bound .open α} :
--     ((succ lower)...(succ upper)).toList =
--       (lower...upper).toList.map succ := by
--   apply eq_of_pairwise_lt_of_mem_iff_mem (lt := UpwardEnumerable.LT) (asymm := ?_)
--   · apply pairwise_toList_upwardEnumerableLt
--   · apply List.Pairwise.map (R := UpwardEnumerable.LT) (S := UpwardEnumerable.LT)
--     · intro a b
--       exact UpwardEnumerable.succ_lt_succ_iff.mpr
--     · apply pairwise_toList_upwardEnumerableLt
--   · simp only [List.mem_map, mem_toList_iff_mem]
--     intro a
--     rw [mem_Rco_succ_succ_iff]
--     constructor
--     · rintro ⟨a, rfl, h⟩
--       exact ⟨a, h, rfl⟩
--     · rintro ⟨a, h, h'⟩
--       exact ⟨_, h'.symm, h⟩
--   · exact ⟨fun _ _ => UpwardEnumerable.not_gt_of_lt⟩

public theorem toList_succ_succ_eq_map [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [InfinitelyUpwardEnumerable α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo hi : α} :
    ((succ lo)...=(succ hi)).toList =
      (lo...=hi).toList.map succ := by
  apply eq_of_pairwise_lt_of_mem_iff_mem (lt := UpwardEnumerable.LT)
  · exact pairwise_toList_upwardEnumerableLt
  · apply List.Pairwise.map (R := UpwardEnumerable.LT) (S := UpwardEnumerable.LT)
    · exact fun _ _ => UpwardEnumerable.succ_lt_succ_iff.mpr
    · exact pairwise_toList_upwardEnumerableLt
  · simp [List.mem_map, mem_toList_iff_mem, mem_succ_succ_iff, eq_comm, and_comm]

@[deprecated Rcc.toList_succ_succ_eq_map (since := "2025-08-22")]
public theorem ClosedOpen.toList_succ_succ_eq_map [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [InfinitelyUpwardEnumerable α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo hi : α} :
    ((succ lo)...=(succ hi)).toList =
      (lo...=hi).toList.map succ :=
  Rcc.toList_succ_succ_eq_map

public theorem forIn'_eq_forIn'_toList [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toList init (fun a ha acc => f a (mem_toList_iff_mem.mp ha) acc) := by
  simp [Internal.forIn'_eq_forIn'_iter, Internal.toList_eq_toList_iter,
    Iter.forIn'_eq_forIn'_toList]

public theorem forIn'_toList_eq_forIn' [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toList init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toList_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toList]

public theorem mem_of_mem_Roc [LE α] [LT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {a b : α}
    (hrb : r.lower ≤ b)
    (hmem : a ∈ b<...=r.upper) :
    a ∈ r := by
  haveI := UpwardEnumerable.instLETransOfLawfulUpwardEnumerableLE (α := α)
  refine ⟨le_trans hrb ?_, hmem.2⟩
  simp only [Membership.mem, LawfulUpwardEnumerableLE.le_iff, LawfulUpwardEnumerableLT.lt_iff] at hmem ⊢
  exact UpwardEnumerable.le_of_lt hmem.1

-- public theorem SupportsLowerBound.isSatisfied_init? {sl} [UpwardEnumerable α]
--     [SupportsLowerBound sl α] [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
--     [LawfulUpwardEnumerableLowerBound sl α]
--     {bound : Bound sl α} {a : α} (h : init? bound = some a) :
--     SupportsLowerBound.IsSatisfied bound a := by
--   simp only [LawfulUpwardEnumerableLowerBound.isSatisfied_iff]
--   exact ⟨a, h, UpwardEnumerable.le_refl _⟩

public theorem forIn'_eq_match_Roc [LE α] [DecidableLE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLE α]
    [Rxc.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {γ : Type u} {init : γ} {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f = if hu : r.lower ≤ r.upper then do
        have hle : r.lower ≤ r.lower := by
          simpa [UpwardEnumerable.le_iff] using UpwardEnumerable.le_refl _
        match ← f r.lower ⟨hle, hu⟩ init with
        | .yield c =>
          ForIn'.forIn' (α := α) (β := γ) (r.lower<...=r.upper) c
            (fun a ha acc => f a (mem_of_mem_Roc hle ha) acc)
        | .done c => return c
      else
        return init := by
  apply Eq.symm
  rw [Internal.forIn'_eq_forIn'_iter, Iter.forIn'_eq_match_step]
  simp only [Rxc.Iterator.step_eq_step, Rxc.Iterator.step, Internal.iter]
  split
  · apply bind_congr; intro step
    split <;> simp [Roc.Internal.forIn'_eq_forIn'_iter, Roc.Internal.iter]
  · simp

public theorem isEmpty_iff_forall_not_mem [LE α] [DecidableLE α] [UpwardEnumerable α]
    [Rxc.HasSize α] [Rxc.LawfulHasSize α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.isEmpty ↔ ∀ a, ¬ a ∈ r := by
  simp only [isEmpty, decide_eq_true_eq]
  constructor
  · rintro h a ⟨hl, hu⟩
    simp only [UpwardEnumerable.le_iff] at h hl hu
    exact h.elim (UpwardEnumerable.le_trans hl hu)
  · intro h hi
    refine h r.lower ⟨?_, hi⟩
    simpa [UpwardEnumerable.le_iff] using UpwardEnumerable.le_refl _

end Rcc

namespace Rco

variable {r : Rco α}

public theorem toList_eq_match [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.toList = if r.lower < r.upper then
        r.lower :: (r.lower<...<r.upper).toList
      else
        [] := by
  rw [Internal.toList_eq_toList_iter, Rxo.Iterator.toList_eq_match]; rfl

public theorem toList_eq_nil_iff [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.toList = [] ↔ ¬ (r.lower < r.upper) := by
  rw [Internal.toList_eq_toList_iter, Rxo.Iterator.toList_eq_match, Internal.iter]
  simp only
  split <;> rename_i heq <;> simp [heq]

public theorem mem_toList_iff_mem [LE α] [DecidableLE α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLE α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {a : α} : a ∈ r.toList ↔ a ∈ r := by
  rw [Internal.toList_eq_toList_iter, Iter.mem_toList_iff_isPlausibleIndirectOutput,
    Internal.isPlausibleIndirectOutput_iter_iff]

-- public theorem BoundedUpwardEnumerable.init?_succ?_closed [UpwardEnumerable α]
--     [LawfulUpwardEnumerable α] {lower lower' : Bound .closed α}
--     (h : UpwardEnumerable.succ? lower = some lower') :
--     init? lower' = (init? lower).bind UpwardEnumerable.succ? := by
--   cases h : init? lower <;> rename_i ilower <;> cases h' : init? lower' <;> rename_i ilower'
--   · simp
--   · simp [init?] at h
--   · simp [init?] at h'
--   · simp_all [init?]

-- @[deprecated BoundedUpwardEnumerable.init?_succ?_closed (since := "2025-08-22")]
-- public theorem BoundedUpwardEnumerable.Closed.init?_succ [UpwardEnumerable α]
--     [LawfulUpwardEnumerable α] {lower lower' : Bound .closed α}
--     (h : UpwardEnumerable.succ? lower = some lower') :
--     init? lower' = (init? lower).bind UpwardEnumerable.succ? :=
--   init?_succ?_closed h

public theorem pairwise_toList_upwardEnumerableLt [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => UpwardEnumerable.LT a b) := by
  rw [Internal.toList_eq_toList_iter]
  apply Rxo.Iterator.pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_ne [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a ≠ b) :=
  List.Pairwise.imp (fun hlt => UpwardEnumerable.ne_of_lt hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_lt [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a < b) :=
  List.Pairwise.imp
    (fun hlt => (LawfulUpwardEnumerableLT.lt_iff ..).mpr hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_le [LE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLT α]
    [LawfulUpwardEnumerableLE α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a ≤ b) :=
  pairwise_toList_upwardEnumerableLt
    |> List.Pairwise.imp UpwardEnumerable.le_of_lt
    |> List.Pairwise.imp (fun hle => (UpwardEnumerable.le_iff ..).mpr hle)

-- public theorem mem_Rco_succ_succ_iff [LE α] [DecidableLE α] [UpwardEnumerable α]
--     [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [InfinitelyUpwardEnumerable α]
--     [HasFiniteRanges .open α] [LawfulUpwardEnumerable α] [LawfulOpenUpperBound α]
--     {lower : Bound .closed α} {upper : Bound .open α} {a : α} :
--     (a ∈ (succ lower)...(succ upper)) ↔ ∃ a', a = succ a' ∧ a' ∈ lower...upper := by
--   simp [Membership.mem, LawfulUpwardEnumerableLowerBound.isSatisfied_iff,
--     init?, LawfulOpenUpperBound.isSatisfied_iff_le]
--   rw [← Option.some_get (InfinitelyUpwardEnumerable.isSome_succ? _)]
--   simp only [Option.some.injEq, ← UpwardEnumerable.succ.eq_def]
--   simp
--   constructor
--   · rintro ⟨⟨n, hn⟩, h⟩
--     rw [succMany?_eq_some_iff_succMany, ← succMany_one, ← succMany_add, Nat.add_comm, succMany_add,
--       succMany_one] at hn
--     rw [← hn]
--     refine ⟨succMany n lower, rfl, ?_, ?_⟩
--     · exact ⟨n, by simp [succMany_eq_get]⟩
--     · obtain ⟨m, hm⟩ := h
--       refine ⟨m, ?_⟩
--       rw [succMany?_eq_some_iff_succMany] at hm ⊢
--       rwa [← hn, ← succMany_one, ← succMany_add, Nat.add_comm, succMany_add, succMany_one,
--         succ_eq_succ_iff] at hm
--   · rintro ⟨a', rfl, hl, hu⟩
--     simp [UpwardEnumerable.succ_le_succ_iff, UpwardEnumerable.succ_lt_succ_iff]
--     exact ⟨hl, hu⟩

public theorem mem_succ_succ_iff [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLE α]
    [InfinitelyUpwardEnumerable α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo hi a : α} :
    (a ∈ (succ lo)...(succ hi)) ↔ ∃ a', a = succ a' ∧ a' ∈ lo...hi := by
  simp [Membership.mem, LawfulUpwardEnumerableLT.lt_iff, LawfulUpwardEnumerableLE.le_iff]
  constructor
  · intro h
    obtain ⟨a', rfl, ha'⟩ := UpwardEnumerable.exists_of_succ_le h.1
    exact ⟨a', rfl, ha', UpwardEnumerable.succ_lt_succ_iff.mp h.2⟩
  · rintro ⟨a', rfl, hl, hu⟩
    simp only [UpwardEnumerable.succ_le_succ_iff, UpwardEnumerable.succ_lt_succ_iff]
    exact ⟨hl, hu⟩

public theorem succ_mem_succ_succ_iff [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [InfinitelyUpwardEnumerable α] [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo hi a : α} :
    (succ a ∈ (succ lo)...(succ hi)) ↔ a ∈ lo...hi := by
  simp [mem_succ_succ_iff, UpwardEnumerable.succ_inj]

-- public theorem toList_Rco_succ_succ_eq_map [UpwardEnumerable α] [SupportsLowerBound .closed α]
--     [LinearlyUpwardEnumerable α] [InfinitelyUpwardEnumerable α] [SupportsUpperBound .open α]
--     [HasFiniteRanges .open α] [LawfulUpwardEnumerable α] [LawfulOpenUpperBound α]
--     [LawfulUpwardEnumerableLowerBound .closed α] [LawfulUpwardEnumerableUpperBound .open α]
--     {lower : Bound .closed α} {upper : Bound .open α} :
--     ((succ lower)...(succ upper)).toList =
--       (lower...upper).toList.map succ := by
--   apply eq_of_pairwise_lt_of_mem_iff_mem (lt := UpwardEnumerable.LT) (asymm := ?_)
--   · apply pairwise_toList_upwardEnumerableLt
--   · apply List.Pairwise.map (R := UpwardEnumerable.LT) (S := UpwardEnumerable.LT)
--     · intro a b
--       exact UpwardEnumerable.succ_lt_succ_iff.mpr
--     · apply pairwise_toList_upwardEnumerableLt
--   · simp only [List.mem_map, mem_toList_iff_mem]
--     intro a
--     rw [mem_Rco_succ_succ_iff]
--     constructor
--     · rintro ⟨a, rfl, h⟩
--       exact ⟨a, h, rfl⟩
--     · rintro ⟨a, h, h'⟩
--       exact ⟨_, h'.symm, h⟩
--   · exact ⟨fun _ _ => UpwardEnumerable.not_gt_of_lt⟩

public theorem toList_succ_succ_eq_map [LE α] [DecidableLE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α] [InfinitelyUpwardEnumerable α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {lo hi : α} :
    ((succ lo)...(succ hi)).toList =
      (lo...hi).toList.map succ := by
  apply eq_of_pairwise_lt_of_mem_iff_mem (lt := UpwardEnumerable.LT)
  · exact pairwise_toList_upwardEnumerableLt
  · apply List.Pairwise.map (R := UpwardEnumerable.LT) (S := UpwardEnumerable.LT)
    · exact fun _ _ => UpwardEnumerable.succ_lt_succ_iff.mpr
    · exact pairwise_toList_upwardEnumerableLt
  · simp [List.mem_map, mem_toList_iff_mem, mem_succ_succ_iff, eq_comm, and_comm]

public theorem forIn'_eq_forIn'_toList [LE α] [DecidableLE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toList init (fun a ha acc => f a (mem_toList_iff_mem.mp ha) acc) := by
  simp [Internal.forIn'_eq_forIn'_iter, Internal.toList_eq_toList_iter,
    Iter.forIn'_eq_forIn'_toList]

public theorem forIn'_toList_eq_forIn' [LE α] [DecidableLE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toList init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toList_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toList]

public theorem mem_of_mem_Roo [LE α] [LT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {a b : α} (hrb : r.lower ≤ b) (hmem : a ∈ b<...r.upper) :
    a ∈ r := by
  haveI := UpwardEnumerable.instLETransOfLawfulUpwardEnumerableLE (α := α)
  refine ⟨le_trans hrb ?_, hmem.2⟩
  simp only [Membership.mem, LawfulUpwardEnumerableLE.le_iff, LawfulUpwardEnumerableLT.lt_iff] at hmem ⊢
  exact UpwardEnumerable.le_of_lt hmem.1

-- public theorem SupportsLowerBound.isSatisfied_init? {sl} [UpwardEnumerable α]
--     [SupportsLowerBound sl α] [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
--     [LawfulUpwardEnumerableLowerBound sl α]
--     {bound : Bound sl α} {a : α} (h : init? bound = some a) :
--     SupportsLowerBound.IsSatisfied bound a := by
--   simp only [LawfulUpwardEnumerableLowerBound.isSatisfied_iff]
--   exact ⟨a, h, UpwardEnumerable.le_refl _⟩

public theorem forIn'_eq_match_Roo [LE α] [DecidableLE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLE α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {γ : Type u} {init : γ} {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f = if hu : r.lower < r.upper then do
        have hle : r.lower ≤ r.lower := by
          simpa [UpwardEnumerable.le_iff] using UpwardEnumerable.le_refl _
        match ← f r.lower ⟨hle, hu⟩ init with
        | .yield c =>
          ForIn'.forIn' (α := α) (β := γ) (r.lower<...r.upper) c
            (fun a ha acc => f a (mem_of_mem_Roo hle ha) acc)
        | .done c => return c
      else
        return init := by
  apply Eq.symm
  rw [Internal.forIn'_eq_forIn'_iter, Iter.forIn'_eq_match_step]
  simp only [Rxo.Iterator.step_eq_step, Rxo.Iterator.step, Internal.iter]
  split
  · apply bind_congr; intro step
    split <;> simp [Roo.Internal.forIn'_eq_forIn'_iter, Roo.Internal.iter]
  · simp

public theorem isEmpty_iff_forall_not_mem [LE α] [LT α] [DecidableLT α] [UpwardEnumerable α]
    [Rxo.HasSize α] [Rxo.LawfulHasSize α] [LawfulUpwardEnumerableLE α]
    [LawfulUpwardEnumerableLT α] [Rxo.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.isEmpty ↔ ∀ a, ¬ a ∈ r := by
  simp only [isEmpty, decide_eq_true_eq]
  constructor
  · rintro h a ⟨hl, hu⟩
    simp only [UpwardEnumerable.le_iff, UpwardEnumerable.lt_iff] at h hl hu
    exact h.elim (UpwardEnumerable.lt_of_le_of_lt hl hu)
  · intro h hi
    refine h r.lower ⟨?_, hi⟩
    simpa [UpwardEnumerable.le_iff] using UpwardEnumerable.le_refl _

end Rco

namespace Rci

variable {r : Rci α}

public theorem toList_eq_match [LE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList = r.lower :: (r.lower<...*).toList := by
  rw [Internal.toList_eq_toList_iter, Rxi.Iterator.toList_eq_match]; rfl

public theorem toList_ne_nil [LE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.toList ≠ [] := by
  rw [Internal.toList_eq_toList_iter, Rxi.Iterator.toList_eq_match, Internal.iter]
  simp

public theorem mem_toList_iff_mem [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {a : α} : a ∈ r.toList ↔ a ∈ r := by
  rw [Internal.toList_eq_toList_iter, Iter.mem_toList_iff_isPlausibleIndirectOutput,
    Internal.isPlausibleIndirectOutput_iter_iff]

-- public theorem BoundedUpwardEnumerable.init?_succ?_closed [UpwardEnumerable α]
--     [LawfulUpwardEnumerable α] {lower lower' : Bound .closed α}
--     (h : UpwardEnumerable.succ? lower = some lower') :
--     init? lower' = (init? lower).bind UpwardEnumerable.succ? := by
--   cases h : init? lower <;> rename_i ilower <;> cases h' : init? lower' <;> rename_i ilower'
--   · simp
--   · simp [init?] at h
--   · simp [init?] at h'
--   · simp_all [init?]

-- @[deprecated BoundedUpwardEnumerable.init?_succ?_closed (since := "2025-08-22")]
-- public theorem BoundedUpwardEnumerable.Closed.init?_succ [UpwardEnumerable α]
--     [LawfulUpwardEnumerable α] {lower lower' : Bound .closed α}
--     (h : UpwardEnumerable.succ? lower = some lower') :
--     init? lower' = (init? lower).bind UpwardEnumerable.succ? :=
--   init?_succ?_closed h

public theorem pairwise_toList_upwardEnumerableLt [LE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => UpwardEnumerable.LT a b) := by
  rw [Internal.toList_eq_toList_iter]
  apply Rxi.Iterator.pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_ne [LE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a ≠ b) :=
  List.Pairwise.imp (fun hlt => UpwardEnumerable.ne_of_lt hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_lt [LE α] [LT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α]
    [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a < b) :=
  List.Pairwise.imp
    (fun hlt => (LawfulUpwardEnumerableLT.lt_iff ..).mpr hlt) pairwise_toList_upwardEnumerableLt

public theorem pairwise_toList_le [LE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] :
    r.toList.Pairwise (fun a b => a ≤ b) :=
  pairwise_toList_upwardEnumerableLt
    |> List.Pairwise.imp UpwardEnumerable.le_of_lt
    |> List.Pairwise.imp (fun hle => (UpwardEnumerable.le_iff ..).mpr hle)

-- public theorem mem_Rci_succ_succ_iff [LE α] [DecidableLE α] [UpwardEnumerable α]
--     [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [InfinitelyUpwardEnumerable α]
--     [HasFiniteRanges .open α] [LawfulUpwardEnumerable α] [LawfulOpenUpperBound α]
--     {lower : Bound .closed α} {upper : Bound .open α} {a : α} :
--     (a ∈ (succ lower)...(succ upper)) ↔ ∃ a', a = succ a' ∧ a' ∈ lower...upper := by
--   simp [Membership.mem, LawfulUpwardEnumerableLowerBound.isSatisfied_iff,
--     init?, LawfulOpenUpperBound.isSatisfied_iff_le]
--   rw [← Option.some_get (InfinitelyUpwardEnumerable.isSome_succ? _)]
--   simp only [Option.some.injEq, ← UpwardEnumerable.succ.eq_def]
--   simp
--   constructor
--   · rintro ⟨⟨n, hn⟩, h⟩
--     rw [succMany?_eq_some_iff_succMany, ← succMany_one, ← succMany_add, Nat.add_comm, succMany_add,
--       succMany_one] at hn
--     rw [← hn]
--     refine ⟨succMany n lower, rfl, ?_, ?_⟩
--     · exact ⟨n, by simp [succMany_eq_get]⟩
--     · obtain ⟨m, hm⟩ := h
--       refine ⟨m, ?_⟩
--       rw [succMany?_eq_some_iff_succMany] at hm ⊢
--       rwa [← hn, ← succMany_one, ← succMany_add, Nat.add_comm, succMany_add, succMany_one,
--         succ_eq_succ_iff] at hm
--   · rintro ⟨a', rfl, hl, hu⟩
--     simp [UpwardEnumerable.succ_le_succ_iff, UpwardEnumerable.succ_lt_succ_iff]
--     exact ⟨hl, hu⟩

public theorem mem_succ_iff [LE α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [InfinitelyUpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo a : α} :
    (a ∈ (succ lo)...*) ↔ ∃ a', a = succ a' ∧ a' ∈ lo...* := by
  simp [Membership.mem, LawfulUpwardEnumerableLE.le_iff]
  constructor
  · intro h
    obtain ⟨a', rfl, ha'⟩ := UpwardEnumerable.exists_of_succ_le h
    exact ⟨a', rfl, UpwardEnumerable.succ_le_succ_iff.mp h⟩
  · rintro ⟨a', rfl, hl, hu⟩
    simp only [UpwardEnumerable.succ_le_succ_iff, UpwardEnumerable.succ_le_succ_iff]
    exact ⟨hl, hu⟩

public theorem succ_mem_succ_succ_iff [LE α] [UpwardEnumerable α]
    [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [InfinitelyUpwardEnumerable α] [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α] {lo a : α} :
    (succ a ∈ (succ lo)...*) ↔ a ∈ lo...* := by
  simp [mem_succ_iff, UpwardEnumerable.succ_inj]

-- public theorem toList_Rci_succ_succ_eq_map [UpwardEnumerable α] [SupportsLowerBound .closed α]
--     [LinearlyUpwardEnumerable α] [InfinitelyUpwardEnumerable α] [SupportsUpperBound .open α]
--     [HasFiniteRanges .open α] [LawfulUpwardEnumerable α] [LawfulOpenUpperBound α]
--     [LawfulUpwardEnumerableLowerBound .closed α] [LawfulUpwardEnumerableUpperBound .open α]
--     {lower : Bound .closed α} {upper : Bound .open α} :
--     ((succ lower)...(succ upper)).toList =
--       (lower...upper).toList.map succ := by
--   apply eq_of_pairwise_lt_of_mem_iff_mem (lt := UpwardEnumerable.LT) (asymm := ?_)
--   · apply pairwise_toList_upwardEnumerableLt
--   · apply List.Pairwise.map (R := UpwardEnumerable.LT) (S := UpwardEnumerable.LT)
--     · intro a b
--       exact UpwardEnumerable.succ_lt_succ_iff.mpr
--     · apply pairwise_toList_upwardEnumerableLt
--   · simp only [List.mem_map, mem_toList_iff_mem]
--     intro a
--     rw [mem_Rci_succ_succ_iff]
--     constructor
--     · rintro ⟨a, rfl, h⟩
--       exact ⟨a, h, rfl⟩
--     · rintro ⟨a, h, h'⟩
--       exact ⟨_, h'.symm, h⟩
--   · exact ⟨fun _ _ => UpwardEnumerable.not_gt_of_lt⟩

public theorem toList_succ_succ_eq_map [LE α] [DecidableLE α]
    [UpwardEnumerable α] [LinearlyUpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [InfinitelyUpwardEnumerable α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {lo : α} :
    ((succ lo)...*).toList = (lo...*).toList.map succ := by
  apply eq_of_pairwise_lt_of_mem_iff_mem (lt := UpwardEnumerable.LT)
  · exact pairwise_toList_upwardEnumerableLt
  · apply List.Pairwise.map (R := UpwardEnumerable.LT) (S := UpwardEnumerable.LT)
    · exact fun _ _ => UpwardEnumerable.succ_lt_succ_iff.mpr
    · exact pairwise_toList_upwardEnumerableLt
  · simp [List.mem_map, mem_toList_iff_mem, mem_succ_iff, eq_comm, and_comm]

public theorem forIn'_eq_forIn'_toList [LE α] [DecidableLE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → a ∈ r → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f =
      ForIn'.forIn' r.toList init (fun a ha acc => f a (mem_toList_iff_mem.mp ha) acc) := by
  simp [Internal.forIn'_eq_forIn'_iter, Internal.toList_eq_toList_iter,
    Iter.forIn'_eq_forIn'_toList]

public theorem forIn'_toList_eq_forIn' [LE α] [DecidableLE α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLE α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {γ : Type u} {init : γ} {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r.toList init f =
      ForIn'.forIn' r init (fun a ha acc => f a (mem_toList_iff_mem.mpr ha) acc) := by
  simp [forIn'_eq_forIn'_toList]

public theorem mem_of_mem_Roi [LE α] [LT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] {a b : α} (hrb : r.lower ≤ b) (hmem : a ∈ b<...*) :
    a ∈ r := by
  haveI := UpwardEnumerable.instLETransOfLawfulUpwardEnumerableLE (α := α)
  refine le_trans hrb ?_
  simp only [Membership.mem, LawfulUpwardEnumerableLE.le_iff, LawfulUpwardEnumerableLT.lt_iff] at hmem ⊢
  exact UpwardEnumerable.le_of_lt hmem

-- public theorem SupportsLowerBound.isSatisfied_init? {sl} [UpwardEnumerable α]
--     [SupportsLowerBound sl α] [BoundedUpwardEnumerable sl α] [LawfulUpwardEnumerable α]
--     [LawfulUpwardEnumerableLowerBound sl α]
--     {bound : Bound sl α} {a : α} (h : init? bound = some a) :
--     SupportsLowerBound.IsSatisfied bound a := by
--   simp only [LawfulUpwardEnumerableLowerBound.isSatisfied_iff]
--   exact ⟨a, h, UpwardEnumerable.le_refl _⟩

public theorem forIn'_eq_match_Roi [LE α] [DecidableLE α] [LT α] [DecidableLT α]
    [UpwardEnumerable α] [LawfulUpwardEnumerableLT α] [LawfulUpwardEnumerableLE α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {m : Type u → Type w} [Monad m] [LawfulMonad m]
    {γ : Type u} {init : γ} {f : (a : α) → _ → γ → m (ForInStep γ)} :
    ForIn'.forIn' r init f = do
      have hle : r.lower ≤ r.lower := by
        simpa [UpwardEnumerable.le_iff] using UpwardEnumerable.le_refl _
      match ← f r.lower hle init with
      | .yield c =>
        ForIn'.forIn' (α := α) (β := γ) (r.lower<...*) c
          (fun a ha acc => f a (mem_of_mem_Roi hle ha) acc)
      | .done c => return c := by
  apply Eq.symm
  rw [Internal.forIn'_eq_forIn'_iter, Iter.forIn'_eq_match_step]
  simp only [Rxi.Iterator.step_eq_step, Rxi.Iterator.step, Internal.iter]
  apply bind_congr; intro step
  split <;> simp [Roi.Internal.forIn'_eq_forIn'_iter, Roi.Internal.iter]

public theorem isEmpty_iff_forall_not_mem [LE α] [UpwardEnumerable α]
    [Rxi.HasSize α] [Rxi.LawfulHasSize α] [LawfulUpwardEnumerableLE α] [Rxi.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α] :
    r.isEmpty ↔ ∀ a, ¬ a ∈ r := by
  simp only [isEmpty, Bool.false_eq_true, false_iff, Classical.not_forall, Classical.not_not]
  exact ⟨r.lower, by simpa [← UpwardEnumerable.le_iff] using UpwardEnumerable.le_refl (α := α) _⟩

end Rci

private theorem Internal.iter_Roc_eq_iter_Rcc_of_isSome_succ?
    [LE α] [UpwardEnumerable α] [LawfulUpwardEnumerable α] {lo hi : α}
    (h : (UpwardEnumerable.succ? lo).isSome) :
    Roc.Internal.iter (lo<...=hi) =
      Rcc.Internal.iter ((UpwardEnumerable.succ? lo |>.get h)...=hi) := by
  simp [Roc.Internal.iter, Rcc.Internal.iter]

public theorem toList_Roc_eq_toList_Rcc_of_isSome_succ? [LE α] [DecidableLE α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [Rxc.IsAlwaysFinite α]
    [LawfulUpwardEnumerable α]
    {lo hi : α} (h : (UpwardEnumerable.succ? lo).isSome) :
    (lo<...=hi).toList =
      ((UpwardEnumerable.succ? lo |>.get h)...=hi).toList := by
  simp [Rcc.Internal.toList_eq_toList_iter, Roc.Internal.toList_eq_toList_iter,
    Internal.iter_Roc_eq_iter_Rcc_of_isSome_succ?, h]

private theorem Internal.iter_Roo_eq_iter_Rco_of_isSome_succ?
    [LE α] [LT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] {lo hi : α} (h : (UpwardEnumerable.succ? lo).isSome) :
    Roo.Internal.iter (lo<...hi) =
      Rco.Internal.iter ((UpwardEnumerable.succ? lo |>.get h)...hi) := by
  simp [Roo.Internal.iter, Rco.Internal.iter]

public theorem toList_Roo_eq_toList_Rco_of_isSome_succ? [LE α] [DecidableLE α]
    [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Rxo.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {lo hi : α} (h : (UpwardEnumerable.succ? lo).isSome) :
    (lo<...hi).toList =
      ((UpwardEnumerable.succ? lo |>.get h)...hi).toList := by
  simp [Rco.Internal.toList_eq_toList_iter, Roo.Internal.toList_eq_toList_iter,
    Internal.iter_Roo_eq_iter_Rco_of_isSome_succ?, h]

private theorem Internal.iter_Roi_eq_iter_Rci_of_isSome_succ?
    [LE α] [LT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] {lo : α} (h : (UpwardEnumerable.succ? lo).isSome) :
    Roi.Internal.iter (lo<...*) =
      Rci.Internal.iter ((UpwardEnumerable.succ? lo |>.get h)...*) := by
  simp [Roi.Internal.iter, Rci.Internal.iter]

public theorem toList_Roi_eq_toList_Rci_of_isSome_succ? [LE α] [DecidableLE α]
    [LT α] [DecidableLT α] [UpwardEnumerable α]
    [LawfulUpwardEnumerable α] [LawfulUpwardEnumerableLE α] [LawfulUpwardEnumerableLT α]
    [Rxi.IsAlwaysFinite α] [LawfulUpwardEnumerable α]
    {lo : α} (h : (UpwardEnumerable.succ? lo).isSome) :
    (lo<...*).toList = ((UpwardEnumerable.succ? lo |>.get h)...*).toList := by
  simp [Rci.Internal.toList_eq_toList_iter, Roi.Internal.toList_eq_toList_iter,
    Internal.iter_Roi_eq_iter_Rci_of_isSome_succ?, h]

end Std
