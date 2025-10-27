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
  (Internal.Zipper.iterOfTree m.inner : Iter ((a : α) × β a))

@[inline]
public def keysIter {α : Type u} {β : α → Type u} [Ord α] (m : Raw α β) :=
  (m.iter.map fun e => e.1 : Iter α)

@[inline]
public def valuesIter {α : Type u} {β : Type u} [Ord α](m : Raw α (fun _ => β)) :=
  (m.iter.map fun e => e.2 : Iter β)

public theorem iter_toList [Ord α] (m : Raw α β) :
    m.iter.toList = m.toList := by
  unfold iter
  simp [Raw.toList]
  exact @Internal.Zipper.iterOfTree_toList_eq_toList α β m.inner

public theorem keysIter_toList {α β} [Ord α] (m : Raw α β) :
    m.keysIter.toList = m.keys := by
  unfold keysIter
  unfold keys
  unfold iter
  rw [← Internal.Impl.map_fst_toList_eq_keys]
  exact Internal.Zipper.map_iterOfTree_eq_tree_toList_map m.inner

public theorem valuesIter_toList {α β} [Ord α] (m : Raw α (fun _ => β)) :
    m.valuesIter.toList = m.values := by
  unfold valuesIter
  unfold values
  unfold iter
  rw [Internal.Impl.values_eq_map_snd]
  rw [← Internal.Impl.toList_eq_toListModel]
  exact Internal.Zipper.map_iterOfTree_eq_tree_toList_map m.inner

end Std.DTreeMap.Raw
