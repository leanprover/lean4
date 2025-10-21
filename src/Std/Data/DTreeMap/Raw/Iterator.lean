/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.DTreeMap.Internal.Zipper
public import Std.Data.DTreeMap
namespace Std.DTreeMap.Raw
open Std.Iterators

@[inline]
public def iter {α : Type u} {β : α → Type v} [Ord α] (m : Raw α β) :=
  (Internal.Zipper.iter_of_tree m.inner : Iter ((a : α) × β a))

@[inline]
public def keysIter {α : Type u} {β : α → Type u} [Ord α] (m : Raw α β) :=
  (m.iter.map fun e => e.1 : Iter α)

@[inline]
public def valuesIter {α : Type u} {β : Type u} [Ord α](m : Raw α (fun _ => β)) :=
  (m.iter.map fun e => e.2 : Iter β)

public theorem iter_toList [Ord α] (m : Raw α β) :
    m.iter.toList = m.toList := by
  rw [Internal.Zipper.toList_Zipper]
  unfold iter
  simp [Raw.toList]
  rw [Internal.Zipper.iter_of_tree_toList_eq_zipper_prependMap_toList]

public theorem keysIter_toList {α β} [Ord α] (m : Raw α β) :
    m.keysIter.toList = m.keys := by
  unfold keysIter
  rw [Internal.Zipper.toList_map_Zipper]
  unfold iter
  rw [Internal.Zipper.iter_of_tree_internal_state_eq]
  rw [Internal.Zipper.prependMap_done_toList_eq_toList]
  unfold keys
  simp [Internal.Impl.map_fst_toList_eq_keys]

public theorem valuesIter_toList {α β} [Ord α] (m : Raw α (fun _ => β)) :
    m.valuesIter.toList = m.values := by
  unfold valuesIter
  rw [Internal.Zipper.toList_map_Zipper]
  unfold iter
  rw [Internal.Zipper.iter_of_tree_internal_state_eq]
  rw [Internal.Zipper.prependMap_done_toList_eq_toList]
  unfold values
  simp [Std.DTreeMap.Internal.Impl.values_eq_map_snd, Internal.Impl.toList_eq_toListModel]

end Std.DTreeMap.Raw
