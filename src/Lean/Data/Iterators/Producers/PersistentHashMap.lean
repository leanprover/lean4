/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Array.Subarray
public import Init.Data.Array.Subarray.Split
public import Lean.Data.PersistentHashMap
import Init.Data.Iterators.Consumers
import Init.Omega
import Init.Data.Slice.Array.Lemmas
import Init.Data.Array.Mem
import Init.Data.List.TakeDrop

/-!
# PersistentHashMap iterator

This module provides an iterator for `Lean.PersistentHashMap` that is accessible via
`Lean.PersistentHashMap.iter`.
-/

public section

namespace Lean.PersistentHashMap

open Std Std.Iterators

/--
A zipper for traversing a `PersistentHashMap`. This is an inductive structure
representing the remaining key-value pairs to yield.
-/
inductive Zipper (α : Type u) (β : Type v) where
  /-- No more elements to yield. -/
  | done
  /-- A frame of entries from a trie node. -/
  | consEntries : Subarray (Entry α β (Node α β)) → Zipper α β → Zipper α β
  /-- A frame of key-value pairs from a collision node. -/
  | consCollision : (keys : Subarray α) → (vals : Subarray β) → keys.size = vals.size →
      Zipper α β → Zipper α β

def Zipper.prependNode (node : Node α β) (z : Zipper α β) : Zipper α β :=
  match node with
  | .entries es => .consEntries es.toSubarray z
  | .collision keys vals hsz => .consCollision keys[*...*] vals[*...*] (by simpa) z

@[inline]
def Zipper.step (it : IterM (α := Zipper α β) Id (α × β)) : IterStep (IterM (α := Zipper α β) Id (α × β)) (α × β) :=
  match it.internalState with
  | .done => .done
  | .consEntries es z' =>
    if h : 0 < es.size then
      let z : Zipper α β := .consEntries (es.drop 1) z'
      match es[0] with
      | .null => .skip ⟨z⟩
      | .entry k v => .yield ⟨z⟩ (k, v)
      | .ref node => .skip ⟨z.prependNode node⟩
    else
      .skip ⟨z'⟩
  | .consCollision keys vals hsz z' =>
    if h : 0 < vals.size then
      .yield ⟨.consCollision (keys.drop 1) (vals.drop 1) (by simp [*]) z'⟩ (keys[0], vals[0])
    else
      .skip ⟨z'⟩

instance instIterator : Iterator (Zipper α β) Id (α × β) where
  IsPlausibleStep it step := step = Zipper.step it
  step it := return .deflate <| ⟨Zipper.step it, rfl⟩

/-- Counts the total number of entries reachable from a node, including nested children. -/
def Node.measure (node : Node α β) : Nat :=
  match node with
  | .entries es => measureEntries es 0
  | .collision _ vals _ => vals.size
termination_by (sizeOf node, 0)
where
  /-- Counts the total entries in an entries array starting at index `i`. -/
  measureEntries (es : Array (Entry α β (Node α β))) (i : Nat) : Nat :=
    if h : i < es.size then
      (match h_eq : es[i] with
       | .null => 1
       | .entry _ _ => 1
       | .ref node =>
         have : sizeOf node < sizeOf es := by
           have h1 := Array.sizeOf_get es i h
           rw [h_eq] at h1
           simp +arith at h1
           omega
         2 + Node.measure node) + measureEntries es (i + 1)
    else 0
  termination_by (sizeOf es, es.size - i)
  decreasing_by all_goals simp_wf <;> omega

def Entry.measure (entry : Entry α β (Node α β)) : Nat :=
  match entry with
  | .null => 1
  | .entry _ _ => 1
  | .ref node => 2 + node.measure

/-- Counts entries remaining in a subarray, including nested children. -/
def subarrayMeasure (es : Subarray (Entry α β (Node α β))) : Nat :=
  es.toList.map (·.measure) |>.sum

/-- Counts the total remaining work in a zipper, including entries nested in child nodes. -/
def Zipper.measure : Zipper α β → Nat
  | .done => 0
  | .consEntries es z' => subarrayMeasure es + z'.measure + 1
  | .consCollision _ vals _ z' => vals.size + z'.measure + 1

private theorem subarrayMeasure_cons (es : Subarray (Entry α β (Node α β)))
    (h : 0 < es.size) :
    subarrayMeasure es = es[0].measure + subarrayMeasure (es.drop 1) := by
  simp only [subarrayMeasure, Subarray.toList_drop]
  have hlen : 0 < es.toList.length := by simpa [Subarray.length_toList] using h
  conv => lhs; rw [show es.toList = List.drop 0 es.toList from List.drop_zero.symm]
  rw [List.drop_eq_getElem_cons (by omega)]
  simp [List.map_cons, List.sum_cons, Subarray.getElem_eq_getElem_toList]

private theorem measureEntries_eq_list_sum (es : Array (Entry α β (Node α β))) (i : Nat) :
    Node.measure.measureEntries es i =
      ((es.toList.drop i).map Entry.measure).sum := by
  unfold Node.measure.measureEntries
  split
  · rename_i h
    rw [List.drop_eq_getElem_cons (by simpa using h)]
    simp only [List.map_cons, List.sum_cons]
    rw [measureEntries_eq_list_sum es (i + 1)]
    congr 1
    simp only [Array.getElem_toList]
    cases es[i] <;> simp [Entry.measure]
  · rename_i h
    rw [List.drop_eq_nil_of_le (by simpa using h)]
    simp
  termination_by es.size - i

private theorem subarrayMeasure_toSubarray_eq (nes : Array (Entry α β (Node α β))) :
    subarrayMeasure nes.toSubarray = Node.measure (.entries nes) := by
  simp only [subarrayMeasure, Node.measure]
  have h1 : nes.toSubarray.toList = nes.toList := by
    rw [Subarray.toList_eq_drop_take]
    simp only [Array.size_eq_length_toList, Array.start_toSubarray, le_refl, Nat.min_eq_left,
      Nat.zero_le, Array.stop_toSubarray, Array.array_toSubarray, List.take_length, List.drop_zero]
  have h2 := measureEntries_eq_list_sum nes 0
  simp only [List.drop_zero] at h2
  rw [h1]
  exact h2.symm

private def instFinitenessRelation :
    FinitenessRelation (Zipper α β) Id where
  Rel t' t := t'.internalState.measure < t.internalState.measure
  wf := InvImage.wf _ Nat.lt_wfRel.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, instIterator] at h'
    subst h'
    simp only [Zipper.step] at h
    split at h
    · -- .done: no successor
      simp only [IterStep.successor_done] at h
      exact nomatch h
    · -- .consEntries es z'
      rename_i es z' heq
      split at h
      · -- 0 < es.size
        rename_i hsz
        have h1 := subarrayMeasure_cons es hsz
        match heq_es0 : es[0] with
        | .null =>
          simp only [heq_es0, IterStep.successor_skip, Option.some.injEq] at h; subst h
          simp only [heq, Zipper.measure, heq_es0, Entry.measure] at h1 ⊢; omega
        | .entry k v =>
          simp only [heq_es0, IterStep.successor_yield, Option.some.injEq] at h; subst h
          simp only [heq, Zipper.measure, heq_es0, Entry.measure] at h1 ⊢; omega
        | .ref node =>
          simp only [heq_es0, IterStep.successor_skip, Option.some.injEq] at h; subst h
          simp only [heq_es0, Entry.measure] at h1
          match heq_node : node with
          | .entries nes =>
            simp only [Zipper.prependNode, heq, Zipper.measure]
            have h2 := subarrayMeasure_toSubarray_eq nes
            omega
          | .collision ks vs hsz' =>
            simp only [Zipper.prependNode, heq, Zipper.measure, Array.size_mkSlice_rii]
            simp only [Node.measure] at h1
            omega
      · -- ¬(0 < es.size) → skip to z'
        simp only [IterStep.successor_skip, Option.some.injEq] at h; subst h
        simp only [heq, Zipper.measure]; omega
    · -- .consCollision keys vals hsz z'
      rename_i keys vals hsz_eq z' heq
      split at h
      · -- 0 < vals.size → yield
        simp only [IterStep.successor_yield, Option.some.injEq] at h; subst h
        simp only [heq, Zipper.measure, Subarray.size_drop]; omega
      · -- ¬(0 < vals.size) → skip
        simp only [IterStep.successor_skip, Option.some.injEq] at h; subst h
        simp only [heq, Zipper.measure]; omega

instance instFinite : Finite (Zipper α β) Id :=
  .of_finitenessRelation instFinitenessRelation

@[always_inline, inline]
instance instIteratorLoop {n : Type _ → Type _} [Monad n] :
    IteratorLoop (Zipper α β) Id n :=
  .defaultImplementation

/--
Returns a finite iterator over the key-value pairs of the given `PersistentHashMap`.
The iteration order is unspecified.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
def iter [BEq α] [Hashable α] (map : PersistentHashMap α β) :
    Iter (α := Zipper α β) (α × β) :=
  ⟨Zipper.prependNode map.root .done⟩

end Lean.PersistentHashMap
