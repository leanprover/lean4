/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Std.Data.Iterators
public import Std.Data.DHashMap.Iterator
import all Std.Data.DHashMap.Basic
import all Std.Data.DHashMap.Raw
import all Std.Data.DHashMap.Iterator
import Init.Data.Iterators.Lemmas.Combinators
import Std.Data.DHashMap.Internal.WF
import all Std.Data.DHashMap.Internal.Defs
import Std.Data.DHashMap.RawLemmas
import Std.Data.DHashMap.Lemmas

namespace Std.DHashMap.Internal.AssocList
open Std.Iterators

@[simp]
public theorem step_iter_nil {α : Type u} {β : α → Type v} :
    ((.nil : AssocList α β).iter).step = ⟨.done, rfl⟩ :=
  (rfl)

@[simp]
public theorem step_iter_cons {α : Type u} {β : α → Type v} {k v} {l : AssocList α β} :
    ((AssocList.cons k v l).iter).step = ⟨.yield l.iter ⟨k, v⟩, rfl⟩ :=
  (rfl)

@[simp]
public theorem toList_iter {α : Type u} {β : α → Type v} {l : AssocList α β} :
    l.iter.toList = l.toList := by
  induction l
  · simp [Iter.toList_eq_match_step, step_iter_nil]
  · rw [Iter.toList_eq_match_step, step_iter_cons]
    simp [*]

end Std.DHashMap.Internal.AssocList

namespace Std.DHashMap.Raw
open Std.Iterators

section EntriesIter

variable {α : Type u} {β : α → Type v} {m : Raw α β}

public theorem toList_entriesIter :
    m.entriesIter.toList = m.toList := by
  simp [Raw.entriesIter, Iter.toList_flatMap, Iter.toList_map, Internal.toListModel, List.flatMap,
    Internal.Raw.toList_eq_toListModel]

public theorem toListRev_entriesIter :
    m.entriesIter.toListRev = m.toList.reverse := by
  simp [Iter.toListRev_eq, toList_entriesIter]

public theorem toArray_entriesIter [BEq α] [Hashable α] (h : m.WF) :
    m.entriesIter.toArray = m.toArray := by
  simp [← Iter.toArray_toList, ← Raw.toArray_toList h, toList_entriesIter]

end EntriesIter

section KeysIter

variable {α : Type u} {β : α → Type u} {m : Raw α β}

public theorem toList_keysIter [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.keysIter.toList = m.keys := by
  simp [keysIter, ← map_fst_toList_eq_keys h, toList_entriesIter]

public theorem toListRev_keysIter [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.keysIter.toListRev = m.keys.reverse := by
  simp [Iter.toListRev_eq, toList_keysIter h]

public theorem toArray_keysIter [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.keysIter.toArray = m.keysArray := by
  simp [← Iter.toArray_toList, ← Raw.toArray_keys h, toList_keysIter h]

end KeysIter

section ValuesIter

variable {α β : Type u} {m : Raw α (fun _ => β)}

public theorem toList_valuesIter_eq_toList_map_snd :
    m.valuesIter.toList = m.toList.map Sigma.snd := by
  simp [valuesIter, toList_entriesIter]

public theorem toListRev_valuesIter :
    m.valuesIter.toListRev = (m.toList.map Sigma.snd).reverse := by
  simp [Iter.toListRev_eq, toList_valuesIter_eq_toList_map_snd]

public theorem toArray_valuesIter :
    m.valuesIter.toArray = (m.toList.map Sigma.snd).toArray := by
  simp [← Iter.toArray_toList, toList_valuesIter_eq_toList_map_snd]

end ValuesIter

end Std.DHashMap.Raw

namespace Std.DHashMap
open Std.Iterators

section EntriesIter

variable {α : Type u} {β : α → Type v} [BEq α] [Hashable α] {m : DHashMap α β}

theorem toList_inner :
    m.inner.toList = m.toList :=
  rfl

public theorem toList_entriesIter :
    m.entriesIter.toList = m.toList := by
  simp [entriesIter, Raw.toList_entriesIter, toList_inner]

public theorem toListRev_entriesIter :
    m.entriesIter.toListRev = m.toList.reverse := by
  simp [Iter.toListRev_eq, toList_entriesIter]

public theorem toArray_entriesIter :
    m.entriesIter.toArray = m.toArray := by
  simp [← Iter.toArray_toList, ← toArray_toList, toList_entriesIter]

end EntriesIter

section KeysIter

variable {α : Type u} {β : α → Type u} [BEq α] [Hashable α] {m : DHashMap α β}

theorem keys_inner :
    m.inner.keys = m.keys :=
  rfl

public theorem toList_keysIter [EquivBEq α] [LawfulHashable α] :
    m.keysIter.toList = m.keys := by
  simp [keysIter, Raw.toList_keysIter m.wf, keys_inner]

public theorem toListRev_keysIter [EquivBEq α] [LawfulHashable α] :
    m.keysIter.toListRev = m.keys.reverse := by
  simp [Iter.toListRev_eq, toList_keysIter]

public theorem toArray_keysIter [EquivBEq α] [LawfulHashable α] :
    m.keysIter.toArray = m.keysArray := by
  simp [← Iter.toArray_toList, ← toArray_keys, toList_keysIter]

end KeysIter

section ValuesIter

variable {α : Type u} {β : Type u} [BEq α] [Hashable α] {m : DHashMap α (fun _ => β)}

public theorem toList_valuesIter_eq_toList_map_snd :
    m.valuesIter.toList = m.toList.map Sigma.snd := by
  simp [valuesIter, toList_entriesIter]

public theorem toListRev_valuesIter :
    m.valuesIter.toListRev = (m.toList.map Sigma.snd).reverse := by
  simp [Iter.toListRev_eq, toList_valuesIter_eq_toList_map_snd]

public theorem toArray_valuesIter :
    m.valuesIter.toArray = (m.toList.map Sigma.snd).toArray := by
  simp [← Iter.toArray_toList, toList_valuesIter_eq_toList_map_snd]

end ValuesIter

end Std.DHashMap
