/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Std.Data.Iterators.Producers.Array
public import Init.Data.Iterators.Combinators.FlatMap
public import Std.Data.DHashMap.Basic
public import Std.Data.DHashMap.Internal.AssocList.Iterator
import Init.Data.Iterators.Combinators.FilterMap
import all Std.Data.DHashMap.Internal.AssocList.Basic
import all Std.Data.DHashMap.Internal.Defs
import Init.Data.Iterators.Lemmas.Combinators
import Init.Data.Iterators.Lemmas.Consumers.Collect
import Std.Data.Iterators.Lemmas.Producers.Array
import Init.Omega

/-!
# Iterators on `DHashMap` and `DHashMap.Raw`
-/

namespace Std.DHashMap.Raw

open Std.Iterators

/-- Internal state of an iterator over the occupied cells of a dependent hash map. -/
@[ext, unbox]
public structure RawIterator (α : Type u) (β : α → Type v) where
  /-- The map being traversed. -/
  map : Raw α β
  /-- The next cell to inspect. -/
  pos : Nat

public instance : Iterator (RawIterator α β) Id ((a : α) × β a) where
  IsPlausibleStep it
    | .yield it' _ =>
      it.internalState.map = it'.internalState.map ∧
      it'.internalState.pos = it.internalState.pos + 1 ∧
      it.internalState.pos < it.internalState.map.keyArray.size
    | .skip it' =>
      it.internalState.map = it'.internalState.map ∧
      it'.internalState.pos = it.internalState.pos + 1 ∧
      it.internalState.pos < it.internalState.map.keyArray.size
    | .done => it.internalState.pos ≥ it.internalState.map.keyArray.size
  step it := pure <| .deflate <|
    if h : it.internalState.pos < it.internalState.map.keyArray.size then
      match it.internalState.map.entryAtInBounds? it.internalState.pos h with
      | .none =>
        .skip ⟨⟨it.internalState.map, it.internalState.pos + 1⟩⟩ ⟨rfl, rfl, h⟩
      | .some out =>
        .yield ⟨⟨it.internalState.map, it.internalState.pos + 1⟩⟩ out ⟨rfl, rfl, h⟩
    else
      .done (Nat.not_lt.mp h)

private def RawIterator.finitenessRelation :
    FinitenessRelation (RawIterator α β) Id where
  Rel := InvImage WellFoundedRelation.rel
    (fun it => it.internalState.map.keyArray.size - it.internalState.pos)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step
    · cases h
      obtain ⟨hmap, hpos, hlt⟩ := h'
      rw [hmap] at hlt
      rw [hmap, hpos]
      omega
    · cases h
      obtain ⟨hmap, hpos, hlt⟩ := h'
      rw [hmap] at hlt
      rw [hmap, hpos]
      omega
    · cases h

public instance : Finite (RawIterator α β) Id :=
  Finite.of_finitenessRelation RawIterator.finitenessRelation

public instance {α : Type u} {β : α → Type v} {m : Type (max u v) → Type w}
    [Monad m] : IteratorLoop (RawIterator α β) Id m :=
  .defaultImplementation

/-- Returns an iterator over the occupied cells at or after `pos`. -/
@[inline, expose]
public def iterFrom {α : Type u} {β : α → Type v} (m : Raw α β) (pos : Nat) :=
  (⟨⟨m, pos⟩⟩ : Iter (α := RawIterator α β) ((a : α) × β a))

@[simp]
public theorem buckets_toList {α : Type u} {β : α → Type v} (m : Raw α β) :
    m.buckets.toList = [m.entriesFrom 0] := by
  simp [Raw.buckets]

@[simp]
public theorem toList_iterFrom {α : Type u} {β : α → Type v} (m : Raw α β) (i : Nat) :
    (m.iterFrom i).toList = (m.entriesFrom i).toList := by
  rw [Raw.entriesFrom.eq_def]
  split
  · rename_i h
    cases he : m.entryAtInBounds? i h with
    | none =>
      rw [Iter.toList_eq_match_step]
      simp only [Iter.step_eq, Raw.iterFrom, Iter.toIterM, Id.run_pure,
        Shrink.inflate_deflate]
      rw [dite_eq_left h]
      simp [he]
      change (m.iterFrom (i + 1)).toList = (m.entriesFrom (i + 1)).toList
      exact toList_iterFrom m (i + 1)
    | some e =>
      obtain ⟨k, v⟩ := e
      rw [Iter.toList_eq_match_step]
      simp only [Iter.step_eq, Raw.iterFrom, Iter.toIterM, Id.run_pure,
        Shrink.inflate_deflate]
      rw [dite_eq_left h]
      simp [he]
      change (m.iterFrom (i + 1)).toList = (m.entriesFrom (i + 1)).toList
      exact toList_iterFrom m (i + 1)
  · rename_i h
    rw [Iter.toList_eq_match_step]
    simp [Iter.step_eq, Raw.iterFrom, h]
termination_by m.keyArray.size - i
decreasing_by all_goals omega

/-- Executable initial position for a raw hash-map iterator. -/
@[inline] public def RawIterator.iterStartImpl {α : Type u} {β : α → Type v}
    (_m : Raw α β) : Nat :=
  0

-- This proof-facing zero exposes the list model to the existing iterator simplification theorem.
@[simp]
public noncomputable def RawIterator.iterStart {α : Type u} {β : α → Type v} (m : Raw α β) : Nat :=
  (m.buckets.iter.flatMap fun b => b.iter).toList.length -
    (Internal.toListModel m.buckets).length

private theorem step_assocListIter_nil {α : Type u} {β : α → Type v} :
    ((.nil : Internal.AssocList α β).iter).step = ⟨.done, rfl⟩ := by
  simp [Iter.step_eq, Internal.AssocList.iter]

private theorem step_assocListIter_cons {α : Type u} {β : α → Type v} {k v}
    {l : Internal.AssocList α β} :
    ((Internal.AssocList.cons k v l).iter).step = ⟨.yield l.iter ⟨k, v⟩, rfl⟩ := by
  simp [Iter.step_eq, Internal.AssocList.iter]

private theorem toList_assocListIter {α : Type u} {β : α → Type v}
    (l : Internal.AssocList α β) : l.iter.toList = l.toList := by
  induction l
  · simp [Iter.toList_eq_match_step, step_assocListIter_nil, Internal.AssocList.toList]
  · rw [Iter.toList_eq_match_step, step_assocListIter_cons]
    simp [Internal.AssocList.toList, *]

@[csimp] public theorem RawIterator.iterStart_eq_iterStartImpl :
    @RawIterator.iterStart = @RawIterator.iterStartImpl := by
  funext α β m
  simp [RawIterator.iterStart, RawIterator.iterStartImpl, Iter.toList_flatMap,
    Iter.toList_map, Array.toList_iter, Internal.toListModel, List.flatMap,
    toList_assocListIter, Raw.buckets]

/--
Returns a finite iterator over the entries of a dependent hash map.
The iterator yields the elements of the map in order and then terminates.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
public def iter {α : Type u} {β : α → Type v} (m : Raw α β) :=
  m.iterFrom (RawIterator.iterStart m)

/--
Returns a finite iterator over the keys of a dependent hash map.
The iterator yields the keys in order and then terminates.

The key and value types must live in the same universe.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
public def keysIter {α : Type u} {β : α → Type u} (m : Raw α β) :=
  (m.iter.map fun e => e.1 : Iter α)

/--
Returns a finite iterator over the values of a hash map.
The iterator yields the values in order and then terminates.

The key and value types must live in the same universe.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
public def valuesIter {α : Type u} {β : Type u} (m : Raw α (fun _ => β)) :=
  (m.iter.map fun e => e.2 : Iter β)

end Std.DHashMap.Raw

namespace Std.DHashMap

@[inline, inherit_doc Raw.iter]
public def iter {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (m : DHashMap α β) :=
  (m.1.iter : Iter ((a : α) × β a))

@[inline, inherit_doc Raw.keysIter]
public def keysIter {α : Type u} {β : α → Type u} [BEq α] [Hashable α] (m : DHashMap α β) :=
  (m.1.keysIter : Iter α)

@[inline, inherit_doc Raw.valuesIter]
public def valuesIter {α : Type u} {β : Type u} [BEq α] [Hashable α]
    (m : DHashMap α (fun _ => β)) :=
  (m.iter.map fun e => e.2 : Iter β)

end Std.DHashMap
