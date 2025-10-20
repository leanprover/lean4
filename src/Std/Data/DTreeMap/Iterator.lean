/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.DTreeMap.Raw.Iterator

namespace Std.DTreeMap
open Std.Iterators

@[inline]
public def iter {α : Type u} {β : α → Type v} [Ord α] (m : DTreeMap α β) :=
  Raw.iter ⟨m.inner⟩

@[inline]
public def keysIter {α : Type u} {β : α → Type u} [Ord α] (m : Raw α β) :=
  Raw.keysIter ⟨m.inner⟩

@[inline]
public def valuesIter {α : Type u} {β : Type u} [Ord α](m : Raw α (fun _ => β)) :=
  Raw.valuesIter ⟨m.inner⟩

public theorem iter_toList [Ord α] (m : Raw α β) :
    m.iter.toList = m.toList := Raw.iter_toList ⟨m.inner⟩

public theorem keysIter_toList {α β} [Ord α] (m : Raw α β) :
    m.keysIter.toList = m.keys := Raw.keysIter_toList ⟨m.inner⟩

public theorem valuesIter_toList {α β} [Ord α] (m : Raw α (fun _ => β)) :
    m.valuesIter.toList = m.values := Raw.valuesIter_toList ⟨m.inner⟩

end Std.DTreeMap
