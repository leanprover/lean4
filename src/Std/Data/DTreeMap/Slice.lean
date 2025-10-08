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

set_option linter.all true

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
    | ⟨⟨map, none, bound, pf⟩⟩ => .done rfl

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

end Rxc

public structure RccSliceData (α : Type u) (β : α → Type v)
    (cmp : α → α → Ordering := by exact compare) where
  treeMap : DTreeMap α β cmp
  range : Rcc α

public abbrev RccSlice α β cmp := Slice (RccSliceData α β cmp)

public instance : Rcc.Sliceable (DTreeMap α β cmp) α (RccSlice α β cmp) where
  mkSlice carrier range := ⟨carrier, range⟩

public instance {s : RccSlice α β cmp} : ToIterator s Id ((a : α) × β a) where
  State := RxcIterator α β cmp
  iterMInternal := ⟨⟨s.1.treeMap, s.1.treeMap.getEntryGE? s.1.range.lower, s.1.range.upper,
      by apply DTreeMap.getEntryGE?_getEntryGE?_eq_some⟩⟩

#eval (.ofList [⟨0, 0⟩, ⟨1, 1⟩, ⟨100, 3⟩, ⟨101, 4⟩] : DTreeMap Nat (fun _ => Nat) compare)[2...=102].toList

public theorem step_iter_rccSlice_eq_match {α β} {cmp : α → α → Ordering} [TransCmp cmp] {t : DTreeMap α β cmp} {a b : α} :
    t[a...=b].iter.step = (match t.getEntryGE? a with
      | _ => sorry) := by
  sorry

public theorem step_iter_rccSlice_eq_match {α β} {cmp : α → α → Ordering} [TransCmp cmp] {t : DTreeMap α β cmp} {a b : α} :
    t[a...=b].iter.step = (match t.getEntryGE? a with
      | some next =>
        if (cmp next b).isLE then
          .yield sorry sorry sorry
        else
          .done sorry
      | none =>
        .done sorry) := by
  sorry

theorem rccSlice_toList_eq_map_rcc_toList {α β} {cmp : α → α → Ordering} [TransCmp cmp] {t : DTreeMap α β cmp} {a b : α} :
    t[a...=b].toList = (a...=b).toList
      := by
  sorry
theorem rccSlice_toList_eq_filter_toList {α β} {cmp : α → α → Ordering} [TransCmp cmp] {t : DTreeMap α β cmp} {a b : α} :
    t[a...=b].toList = t.toList.filter (fun e => (cmp a e.fst).isLE ∧ (cmp e.fst b).isLE)
      := by
  induction h : t.toList.length
  · rw [length_toList, ← beq_iff_eq, ← isEmpty_eq_size_eq_zero] at h
    simp [Slice.toList_eq_toList_iter, Slice.iter_eq_toIteratorIter, ToIterator.iter, ToIterator.iterM, ToIterator.iterMInternal]
    rw [DTreeMap.toList_eq_nil]
    simp? [length_toList, ← beq_iff_eq, ← isEmpty_eq_size_eq_zero] at h

end Std.DTreeMap
