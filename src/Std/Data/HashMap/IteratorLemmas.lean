/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Iterators.Lemmas.Combinators

import Std.Data.DHashMap.IteratorLemmas
public import Std.Data.HashMap.Iterator
import all Std.Data.HashMap.Iterator
import Std.Data.HashMap.RawLemmas
import Std.Data.HashMap.Lemmas
import Std.Data.DHashMap.Internal.WF
import all Std.Data.DHashMap.Basic

namespace Std.HashMap.Raw
open Std.Iterators

section EntriesIter

variable {α : Type u} {β : Type v} {m : Raw α β}

theorem toList_inner :
    m.inner.toList = m.toList.map fun e => ⟨e.1, e.2⟩ := by
  simp [toList, DHashMap.Internal.Raw.Const.toList_eq_toListModel_map,
    ← DHashMap.Internal.Raw.toList_eq_toListModel, Function.comp_def]

public theorem toList_entriesIter :
    m.entriesIter.toList = m.toList := by
  simp [Raw.entriesIter, Iter.toList_map, DHashMap.Raw.toList_entriesIter, toList_inner,
    Function.comp_def]

public theorem toListRev_entriesIter :
    m.entriesIter.toListRev = m.toList.reverse := by
  simp [Iter.toListRev_eq, toList_entriesIter]

public theorem toArray_entriesIter [BEq α] [Hashable α] (h : m.WF) :
    m.entriesIter.toArray = m.toArray := by
  simp [← Iter.toArray_toList, ← Raw.toArray_toList h, toList_entriesIter]

end EntriesIter

section KeysIter

variable {α β : Type u} {m : Raw α β}

theorem keys_inner :
    m.inner.keys = m.keys :=
  rfl

public theorem toList_keysIter [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.keysIter.toList = m.keys := by
  simp only [keysIter, ← map_fst_toList_eq_keys h, DHashMap.Raw.toList_keysIter h.out]
  simp [HashMap.Raw.map_fst_toList_eq_keys h, keys_inner]

public theorem toListRev_keysIter [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.keysIter.toListRev = m.keys.reverse := by
  simp [Iter.toListRev_eq, toList_keysIter h]

public theorem toArray_keysIter [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (h : m.WF) :
    m.keysIter.toArray = m.keysArray := by
  simp [← Iter.toArray_toList, ← Raw.toArray_keys h, toList_keysIter h]

end KeysIter

section ValuesIter

variable {α β : Type u} {m : Raw α β}

public theorem toList_valuesIter_eq_toList_map_snd :
    m.valuesIter.toList = m.toList.map Prod.snd := by
  simp [valuesIter, DHashMap.Raw.toList_valuesIter_eq_toList_map_snd,
    DHashMap.Internal.Raw.toList_eq_toListModel, toList,
    DHashMap.Internal.Raw.Const.toList_eq_toListModel_map]

public theorem toListRev_valuesIter :
    m.valuesIter.toListRev = (m.toList.map Prod.snd).reverse := by
  simp [Iter.toListRev_eq, toList_valuesIter_eq_toList_map_snd]

public theorem toArray_valuesIter :
    m.valuesIter.toArray = (m.toList.map Prod.snd).toArray := by
  simp [← Iter.toArray_toList, toList_valuesIter_eq_toList_map_snd]

end ValuesIter

end Std.HashMap.Raw

namespace Std.HashMap
open Std.Iterators

section EntriesIter

variable {α : Type u} {β : Type v} [BEq α] [Hashable α] {m : HashMap α β}

theorem toList_inner :
    m.inner.toList = m.toList.map fun e => ⟨e.1, e.2⟩ := by
  simp [toList, DHashMap.Const.toList, DHashMap.Internal.Raw.Const.toList_eq_toListModel_map,
    Function.comp_def, DHashMap.toList, DHashMap.Internal.Raw.toList_eq_toListModel]

public theorem toList_entriesIter :
    m.entriesIter.toList = m.toList := by
  simp [entriesIter, DHashMap.toList_entriesIter, toList_inner, Function.comp_def]

public theorem toListRev_entriesIter :
    m.entriesIter.toListRev = m.toList.reverse := by
  simp [Iter.toListRev_eq, toList_entriesIter]

public theorem toArray_entriesIter :
    m.entriesIter.toArray = m.toArray := by
  simp [← Iter.toArray_toList, toList_entriesIter]

end EntriesIter

section KeysIter

theorem keys_inner {α : Type u} {β : Type v} [BEq α] [Hashable α] {m : HashMap α β} :
    m.inner.keys = m.keys :=
  rfl

variable {α : Type u} {β : Type u} [BEq α] [Hashable α] {m : HashMap α β}

public theorem toList_keysIter [EquivBEq α] [LawfulHashable α] :
    m.keysIter.toList = m.keys := by
  simp [keysIter, DHashMap.toList_keysIter, keys_inner]

public theorem toListRev_keysIter [EquivBEq α] [LawfulHashable α] :
    m.keysIter.toListRev = m.keys.reverse := by
  simp [keysIter, DHashMap.toListRev_keysIter, keys_inner]

public theorem toArray_keysIter [EquivBEq α] [LawfulHashable α] :
    m.keysIter.toArray = m.keysArray := by
  simp [← Iter.toArray_toList, keysIter, keysArray, DHashMap.toList_keysIter]

end KeysIter

section ValuesIter

variable {α : Type u} {β : Type u} [BEq α] [Hashable α] {m : HashMap α β}

public theorem toList_valuesIter_eq_toList_map_snd :
    m.valuesIter.toList = m.toList.map Prod.snd := by
  simp [valuesIter, DHashMap.toList_valuesIter_eq_toList_map_snd, toList_inner]

public theorem toListRev_valuesIter :
    m.valuesIter.toListRev = (m.toList.map Prod.snd).reverse := by
  simp [Iter.toListRev_eq, toList_valuesIter_eq_toList_map_snd]

public theorem toArray_valuesIter :
    m.valuesIter.toArray = (m.toList.map Prod.snd).toArray := by
  simp [← Iter.toArray_toList, toList_valuesIter_eq_toList_map_snd]

end ValuesIter

end Std.HashMap
