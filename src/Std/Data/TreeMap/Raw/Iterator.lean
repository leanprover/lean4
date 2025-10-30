/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.DTreeMap.Raw.Iterator
public import Std.Data.TreeMap.Raw.Basic

/-!
# Iterators on `DTreeMap.Raw`
-/

namespace Std.TreeMap.Raw
open Std.Iterators

/--
Returns a finite iterator over the entries of a tree map.
The iterator yields the elements of the map in order and then terminates.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
public def iter {α : Type u} {β : Type v}
    (cmp : α → α → Ordering := by exact compare) (m : Raw α β cmp) :=
  ((m.inner.iter cmp).map fun e => (e.1, e.2) : Iter (α × β))

/--
Returns a finite iterator over the keys of a tree map.
The iterator yields the keys in order and then terminates.

The key and value types must live in the same universe.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
public def keysIter {α : Type u} {β : Type u}
    (cmp : α → α → Ordering := by exact compare) (m : Raw α β cmp) :=
  (DTreeMap.Raw.keysIter cmp m.inner : Iter α)

/--
Returns a finite iterator over the values of a tree map.
The iterator yields the values in order and then terminates.

The key and value types must live in the same universe.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
public def valuesIter {α : Type u} {β : Type u}
    (cmp : α → α → Ordering := by exact compare) (m : Raw α β cmp) :=
  (DTreeMap.Raw.valuesIter cmp m.inner : Iter β)

@[simp]
public theorem iter_toList {α : Type u} {β : Type u} {cmp : α → α → Ordering} (m : Raw α β cmp) :
    ((m.iter cmp).toList) = m.toList := by
  simp only [iter, Iter.toList_map, DTreeMap.Raw.iter_toList]
  simp only [DTreeMap.Raw.toList, DTreeMap.Internal.Impl.toList_eq_toListModel, toList,
    DTreeMap.Raw.Const.toList, DTreeMap.Internal.Impl.Const.toList_eq_toListModel_map]

@[simp]
public theorem keysIter_toList {α β} {cmp : α → α → Ordering} (m : Raw α β cmp) :
    (m.keysIter cmp).toList = m.keys :=
  DTreeMap.Raw.keysIter_toList m.inner

@[simp]
public theorem valuesIter_toList {α β} {cmp : α → α → Ordering} (m : Raw α β cmp) :
    (m.valuesIter cmp).toList = m.values :=
  DTreeMap.Raw.valuesIter_toList m.inner

end Std.TreeMap.Raw
