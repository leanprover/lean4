/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Basic
public import Init.Data.Iterators.Consumers
public import Std.Data.Iterators.Lemmas.Producers.Slice
public import Init.Data.Slice
public import Init.Data.Range.Polymorphic.Basic
public import Std.Data.DTreeMap.Lemmas

namespace Std.DTreeMap
open Std.Iterators

section Rxc

public structure RxcIterator (α : Type u) (β : α → Type v) (cmp : α → α → Ordering) : Type (max u v) where
  treeMap : DTreeMap α β cmp
  next : Option ((a : α) × β a)
  bound : α
  pf : open Classical in next.all fun e => treeMap.getEntryGE? e.fst = some e

variable {α : Type u} {β : α → Type v}

public instance : Iterator (RxcIterator α β cmp) Id ((a : α) × β a) where
  IsPlausibleStep it
    | .yield it' out =>
      (cmp out.fst it.internalState.bound).isLE ∧
        it.internalState.next = some out ∧
        it'.internalState = {
          it.internalState with
          next := it.internalState.treeMap.getEntryGT? out.fst
          pf := by apply DTreeMap.getEntryGE?_getEntryGT?_eq_some }
    | .skip it' => False
    | .done => it.internalState.next.all (cmp ·.fst it.internalState.bound = .gt)
  step
    | ⟨⟨map, some out, bound, pf⟩⟩ =>
      if h : (cmp out.fst bound).isLE then
        pure (.yield ⟨⟨map, map.getEntryGT? out.fst, bound,
            by apply DTreeMap.getEntryGE?_getEntryGT?_eq_some⟩⟩
          out (by simpa using h))
      else
        pure (.done (by simpa using h))
    | ⟨⟨map, none, bound, pf⟩⟩ => pure (.done rfl)

public instance : IteratorCollect (RxcIterator α β cmp) Id Id := .defaultImplementation

public instance : IteratorCollectPartial (RxcIterator α β cmp) Id Id := .defaultImplementation

-- TODO: place this appropriately, same for RangeIterator
private def List.Sublist.filter_mono {l : List α} {P Q : α → Bool} (h : ∀ a, P a → Q a) :
    List.Sublist (l.filter P) (l.filter Q) := by
  apply List.Sublist.trans (l₂ := (l.filter Q).filter P)
  · simp [Bool.and_eq_left_iff_imp.mpr (h _)]
  · apply List.filter_sublist

private def List.length_filter_strict_mono {l : List α} {P Q : α → Bool} {a : α}
    (h : ∀ a, P a → Q a) (ha : a ∈ l) (hPa : ¬ P a) (hQa : Q a) :
    (l.filter P).length < (l.filter Q).length := by
  have hsl : List.Sublist (l.filter P) (l.filter Q) := by
    apply List.Sublist.filter_mono
    exact h
  apply Nat.lt_of_le_of_ne
  · apply List.Sublist.length_le
    exact hsl
  · intro h
    apply hPa
    have heq := List.Sublist.eq_of_length hsl h
    have : a ∈ List.filter Q l := List.mem_filter.mpr ⟨ha, hQa⟩
    rw [← heq, List.mem_filter] at this
    exact this.2

def instFinitenessRelation [TransCmp cmp] : FinitenessRelation (RxcIterator α β cmp) Id where
  rel it' it :=
      (it'.internalState.treeMap.toList.filter (fun e => it'.internalState.next.any fun next => (cmp next.fst e.fst).isLE)).length <
        (it.internalState.treeMap.toList.filter (fun e => it.internalState.next.any fun next => (cmp next.fst e.fst).isLE)).length
  subrelation {it it'} h := by
    obtain ⟨w, h, h'⟩ := h
    simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep] at h'
    cases w
    · cases h
      simp only at h'
      simp only [h']
      apply List.length_filter_strict_mono
      · intro e he
        obtain ⟨e', he'⟩ := (Option.any_eq_true _ _).mp he
        apply TransCmp.isLE_trans ?_ he'.2
        simp only [getEntryGT?_eq_some_iff] at he'
        apply Ordering.isLE_of_eq_lt
        exact he'.1.2.1
      · have := it.internalState.pf
        simp only [getEntryGE?_eq_some_iff, h'.2.1, Option.all_some, decide_eq_true_eq] at this
        exact this.1
      · simp only [Bool.not_eq_true, Option.any_eq_false, getEntryGT?_eq_some_iff, and_imp]
        intro y hy hlt h
        simpa [OrientedCmp.gt_iff_lt] using hlt
      · simpa using ReflCmp.isLE_rfl
    · cases h'
    · cases h
  wf := by
    apply InvImage.wf
    exact Nat.lt_wfRel.wf

@[no_expose]
public instance instFinite [TransCmp cmp] : Finite (RxcIterator α β cmp) Id :=
  .of_finitenessRelation instFinitenessRelation

public theorem step_rxcIterator_eq_match {α β} {cmp : α → α → Ordering} [TransCmp cmp] {it : IterM (α := RxcIterator α β cmp) Id _} :
    it.step = pure (match h : it.internalState.next with
      | some next =>
        if h' : (cmp next.fst it.internalState.bound).isLE then
          .yield ⟨it.internalState.treeMap, it.internalState.treeMap.getEntryGT? next.fst, it.internalState.bound, (by apply getEntryGE?_getEntryGT?_eq_some)⟩ next
            (by simp [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, h', h])
        else
          .done (by simpa [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, h] using h')
      | none =>
        .done (by simp [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, h])) := by
  simp [IterM.step, Iterator.step]
  split
  · simp
    split <;> simp
  · simp

private theorem Option.filter_eq_none_iff_all {α} {o : Option α} {p : α → Bool} :
    o.filter p = none ↔ o.all (! p ·) := by
  simp [Option.all_eq_true]

end Rxc

public structure RocSliceData (α : Type u) (β : α → Type v)
    (cmp : α → α → Ordering := by exact compare) where
  treeMap : DTreeMap α β cmp
  range : Roc α

public abbrev RocSlice α β cmp := Slice (RocSliceData α β cmp)

public instance : Roc.Sliceable (DTreeMap α β cmp) α (RocSlice α β cmp) where
  mkSlice carrier range := ⟨carrier, range⟩

@[always_inline]
public def RocSlice.Internal.iterM (s : RocSlice α β cmp) : IterM (α := RxcIterator α β cmp) Id ((a : α) × β a) :=
  ⟨⟨s.1.treeMap, s.1.treeMap.getEntryGT? s.1.range.lower, s.1.range.upper,
      by apply getEntryGE?_getEntryGT?_eq_some⟩⟩

public instance {s : RocSlice α β cmp} : ToIterator s Id ((a : α) × β a) where
  State := RxcIterator α β cmp
  /-
  There is a good reason to extract the iterator into a separate function `RccSlice.Internal.iterM`:
  The `Iterator` instance on `ToIterator.State` needs to unfold `ToIterator.State`, which requires
  unfolding this `ToIterator` instance. In consequence, the definition of `iterMInternal` is also
  unfolded. Because it is complex and highly dependent, this is not desirable.
  See `Std.Iterators.instIteratorState`.
  -/
  iterMInternal := RocSlice.Internal.iterM s

#eval (.ofList [⟨0, 0⟩, ⟨1, 1⟩, ⟨100, 3⟩, ⟨101, 4⟩] : DTreeMap Nat (fun _ => Nat) compare)[1<...=102].toList

public theorem step_iter_rocSlice_eq_match {α β} {cmp : α → α → Ordering} [TransCmp cmp] {t : DTreeMap α β cmp} {a b : α} :
    t[a<...=b].iter.step = (match h : t.getEntryGT? a with
      | some next =>
        if h' : (cmp next.fst b).isLE then
          .yield ⟨t, t.getEntryGT? next.fst, b, (by apply getEntryGE?_getEntryGT?_eq_some)⟩ next
            (by simp [Iter.IsPlausibleStep, IterM.IsPlausibleStep, Iterator.IsPlausibleStep, Slice.iter_eq_toIteratorIter, ToIterator.iter_eq, RocSlice.Internal.iterM, Roc.Sliceable.mkSlice, Iter.toIterM, IterM.toIter, h', h])
        else
          .done (by simpa [Iter.IsPlausibleStep, IterM.IsPlausibleStep, Iterator.IsPlausibleStep, Slice.iter_eq_toIteratorIter, ToIterator.iter_eq, RocSlice.Internal.iterM, Roc.Sliceable.mkSlice, h] using h')
      | none =>
        .done (by simp [Iter.IsPlausibleStep, IterM.IsPlausibleStep, Iterator.IsPlausibleStep, Slice.iter_eq_toIteratorIter, ToIterator.iter_eq, RocSlice.Internal.iterM, Roc.Sliceable.mkSlice, h])) := by
  simp only [Iter.step, PlausibleIterStep.yield, PlausibleIterStep.done]
  rw [step_rxcIterator_eq_match]
  simp only [PlausibleIterStep.yield, PlausibleIterStep.done, Id.run_pure]
  simp only [RocSlice.Internal.iterM, Iter.toIterM, Slice.iter_eq_toIteratorIter, ToIterator.iter_eq, IterM.toIter]
  simp [Roc.Sliceable.mkSlice]
  split <;> rename_i heq
  · simp only [Slice.iter_eq_toIteratorIter, ToIterator.iter_eq, IterM.toIter, RocSlice.Internal.iterM] at heq
    split <;> split <;> simp_all [IterM.toIter]
  · simp only [Slice.iter_eq_toIteratorIter, ToIterator.iter_eq, IterM.toIter, RocSlice.Internal.iterM] at heq
    split <;> simp_all

public theorem val_step_iter_rocSlice_eq_match {α β} {cmp : α → α → Ordering} [TransCmp cmp] {t : DTreeMap α β cmp} {a b : α} :
    t[a<...=b].iter.step.val = (match (t.getEntryGT? a).filter (fun e => (cmp e.fst b).isLE) with
      | some next =>
        .yield ⟨t, t.getEntryGT? next.fst, b, (by apply getEntryGE?_getEntryGT?_eq_some)⟩ next
      | none =>
        .done) := by
  rw [step_iter_rocSlice_eq_match]
  split <;> split <;> simp_all [Option.filter_some]

public theorem filter_toList_lt_and_isLE {α β} {cmp : α → α → Ordering} [TransCmp cmp] {t : DTreeMap α β cmp} {a b : α} :
    t.toList.filter (fun e => cmp a e.fst = .lt ∧ (cmp e.fst b).isLE) = (match (t.getEntryGT? a).filter (fun e => (cmp e.fst b).isLE) with
      | some next =>
        next :: t.toList.filter (fun e => cmp next.fst e.fst = .lt ∧ (cmp e.fst b).isLE)
      | none =>
        []) := by
  induction hs : t.size
  · rw [← beq_iff_eq, ← DTreeMap.isEmpty_eq_size_eq_zero] at hs
    have : t.toList = [] := by simpa [← DTreeMap.isEmpty_toList] using hs
    simp [getEntryGT?_of_isEmpty hs, this]
  · sorry

public theorem toList_rocSlice_eq_filter_toList {α β} {cmp : α → α → Ordering} [TransCmp cmp]
    {t : DTreeMap α β cmp} {a b : α} :
    t[a<...=b].toList = t.toList.filter (fun e => cmp a e.fst = .lt ∧ (cmp e.fst b).isLE) := by
  rw [filter_toList_lt_and_isLE, Slice.toList_eq_toList_iter, Iter.toList_eq_match_step,
    val_step_iter_rocSlice_eq_match]
  cases Option.filter (fun e => (cmp e.fst b).isLE) (t.getEntryGT? a)
  · simp
  · rename_i next
    suffices h : t[next.fst<...=b].toList = t.toList.filter (fun e => cmp next.fst e.fst = .lt ∧ (cmp e.fst b).isLE) by
      simpa [Slice.toList_eq_toList_iter, Slice.iter_eq_toIteratorIter, ToIterator.iter_eq,
        RocSlice.Internal.iterM, Roc.Sliceable.mkSlice] using h
    apply toList_rocSlice_eq_filter_toList
termination_by (t.toList.filter (fun e => cmp a e.fst = .lt ∧ (cmp e.fst b).isLE)).length
decreasing_by
  rename_i next hnext
  simp only [getEntryGT?_eq_some_iff, Option.filter_eq_some_iff] at hnext
  apply List.length_filter_strict_mono (a := next)
  · simp only [decide_eq_true_eq, and_imp]
    intro e hne heb
    exact ⟨TransCmp.lt_trans hnext.1.2.1 hne, heb⟩
  · exact hnext.1.1
  · simp only [ReflCmp.compare_self, reduceCtorEq, false_and, decide_false, not_false_eq_true]
  · simp only [decide_eq_true_eq]
    exact ⟨hnext.1.2.1, hnext.2⟩

public structure RccSliceData (α : Type u) (β : α → Type v)
    (cmp : α → α → Ordering := by exact compare) where
  treeMap : DTreeMap α β cmp
  range : Rcc α

public abbrev RccSlice α β cmp := Slice (RccSliceData α β cmp)

public instance : Rcc.Sliceable (DTreeMap α β cmp) α (RccSlice α β cmp) where
  mkSlice carrier range := ⟨carrier, range⟩

@[always_inline]
public def RccSlice.Internal.iterM (s : RccSlice α β cmp) : IterM (α := RxcIterator α β cmp) Id ((a : α) × β a) :=
  ⟨⟨s.1.treeMap, s.1.treeMap.getEntryGE? s.1.range.lower, s.1.range.upper,
      by apply getEntryGE?_getEntryGE?_eq_some⟩⟩

public instance {s : RccSlice α β cmp} : ToIterator s Id ((a : α) × β a) where
  State := RxcIterator α β cmp
  /-
  There is a good reason to extract the iterator into a separate function `RccSlice.Internal.iterM`:
  The `Iterator` instance on `ToIterator.State` needs to unfold `ToIterator.State`, which requires
  unfolding this `ToIterator` instance. In consequence, the definition of `iterMInternal` is also
  unfolded. Because it is complex and highly dependent, this is not desirable.
  See `Std.Iterators.instIteratorState`.
  -/
  iterMInternal := RccSlice.Internal.iterM s

#eval (.ofList [⟨0, 0⟩, ⟨1, 1⟩, ⟨100, 3⟩, ⟨101, 4⟩] : DTreeMap Nat (fun _ => Nat) compare)[2...=102].toList

public theorem step_iter_rccSlice_eq_match {α β} {cmp : α → α → Ordering} [TransCmp cmp] {t : DTreeMap α β cmp} {a b : α} :
    t[a...=b].iter.step = (match h : t.getEntryGE? a with
      | some next =>
        if h' : (cmp next.fst b).isLE then
          .yield ⟨t, t.getEntryGT? next.fst, b, (by apply getEntryGE?_getEntryGT?_eq_some)⟩ next
            (by simp [Iter.IsPlausibleStep, IterM.IsPlausibleStep, Iterator.IsPlausibleStep, Slice.iter_eq_toIteratorIter, ToIterator.iter_eq, RccSlice.Internal.iterM, Rcc.Sliceable.mkSlice, Iter.toIterM, IterM.toIter, h', h])
        else
          .done (by simpa [Iter.IsPlausibleStep, IterM.IsPlausibleStep, Iterator.IsPlausibleStep, Slice.iter_eq_toIteratorIter, ToIterator.iter_eq, RccSlice.Internal.iterM, Rcc.Sliceable.mkSlice, h] using h')
      | none =>
        .done (by simp [Iter.IsPlausibleStep, IterM.IsPlausibleStep, Iterator.IsPlausibleStep, Slice.iter_eq_toIteratorIter, ToIterator.iter_eq, RccSlice.Internal.iterM, Rcc.Sliceable.mkSlice, h])) := by
  simp only [Iter.step, PlausibleIterStep.yield, PlausibleIterStep.done]
  rw [step_rxcIterator_eq_match]
  simp only [PlausibleIterStep.yield, PlausibleIterStep.done, Id.run_pure]
  simp only [RccSlice.Internal.iterM, Iter.toIterM, Slice.iter_eq_toIteratorIter, ToIterator.iter_eq, IterM.toIter]
  simp [Rcc.Sliceable.mkSlice]
  split <;> rename_i heq
  · simp only [Slice.iter_eq_toIteratorIter, ToIterator.iter_eq, IterM.toIter, RccSlice.Internal.iterM] at heq
    split <;> split <;> simp_all [IterM.toIter]
  · simp only [Slice.iter_eq_toIteratorIter, ToIterator.iter_eq, IterM.toIter, RccSlice.Internal.iterM] at heq
    split <;> simp_all

public theorem val_step_iter_rccSlice_eq_match {α β} {cmp : α → α → Ordering} [TransCmp cmp] {t : DTreeMap α β cmp} {a b : α} :
    t[a...=b].iter.step.val = (match (t.getEntryGE? a).filter (fun e => (cmp e.fst b).isLE) with
      | some next =>
        .yield ⟨t, t.getEntryGT? next.fst, b, (by apply getEntryGE?_getEntryGT?_eq_some)⟩ next
      | none =>
        .done) := by
  rw [step_iter_rccSlice_eq_match]
  split <;> split <;> simp_all [Option.filter_some]

public theorem filter_toList_isLE_and_isLE {α β} {cmp : α → α → Ordering} [TransCmp cmp] {t : DTreeMap α β cmp} {a b : α} :
    t.toList.filter (fun e => (cmp a e.fst).isLE ∧ (cmp e.fst b).isLE) = (match (t.getEntryGE? a).filter (fun e => (cmp e.fst b).isLE) with
      | some next =>
        next :: t.toList.filter (fun e => cmp next.fst e.fst = .lt ∧ (cmp e.fst b).isLE)
      | none =>
        []) := by
  induction hs : t.size
  · rw [← beq_iff_eq, ← DTreeMap.isEmpty_eq_size_eq_zero] at hs
    have : t.toList = [] := by simpa [← DTreeMap.isEmpty_toList] using hs
    simp [getEntryGE?_of_isEmpty hs, this]
  · sorry

public theorem toList_rccSlice_eq_filter_toList {α β} {cmp : α → α → Ordering} [TransCmp cmp]
    {t : DTreeMap α β cmp} {a b : α} :
    t[a...=b].toList = t.toList.filter (fun e => (cmp a e.fst).isLE ∧ (cmp e.fst b).isLE) := by
  rw [filter_toList_isLE_and_isLE, Slice.toList_eq_toList_iter, Iter.toList_eq_match_step,
    val_step_iter_rccSlice_eq_match]
  cases Option.filter (fun e => (cmp e.fst b).isLE) (t.getEntryGE? a)
  · simp
  · rename_i next
    suffices h : t[next.fst<...=b].toList = t.toList.filter (fun e => cmp next.fst e.fst = .lt ∧ (cmp e.fst b).isLE) by
      simpa [Slice.toList_eq_toList_iter, Slice.iter_eq_toIteratorIter, ToIterator.iter_eq,
        RocSlice.Internal.iterM, Roc.Sliceable.mkSlice] using h
    apply toList_rocSlice_eq_filter_toList

end Std.DTreeMap
