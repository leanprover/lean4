/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.TreeMap.Basic
public import Std.Data.DTreeMap.Iterator
import Init.Data.Iterators.Lemmas.Combinators.FilterMap

/-!
# Iterators on `DTreeMap`
-/

namespace Std.TreeMap
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
    {cmp : α → α → Ordering} (m : TreeMap α β cmp) :=
  (m.inner.iter.map fun e => (e.1, e.2) : Iter (α × β))

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
    {cmp : α → α → Ordering} (m : TreeMap α β cmp) :=
  m.inner.keysIter

/--
Returns a finite iterator over the values of a tree map.
The iterator yields the values in order and then terminates.

The key and value types must live in the same universe.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
public def valuesIter {α : Type u} {β : Type u} {cmp : α → α → Ordering}
    (m : TreeMap α β cmp) :=
  m.inner.valuesIter

@[simp]
public theorem toList_iter {cmp : α → α → Ordering} (m : TreeMap α β cmp) :
    m.iter.toList = m.toList := by
  simp only [iter, Iter.toList_map, DTreeMap.toList_iter, DTreeMap.toList,
    DTreeMap.Internal.Impl.toList_eq_toListModel, toList, DTreeMap.Const.toList,
    DTreeMap.Internal.Impl.Const.toList_eq_toListModel_map]


@[simp]
public theorem keysIter_toList {α β} {cmp : α → α → Ordering} (m : TreeMap α β cmp) :
    m.keysIter.toList = m.keys :=
  m.inner.keysIter_toList

@[simp]
public theorem valuesIter_toList {α β} {cmp : α → α → Ordering} (m : TreeMap α β cmp) :
    m.valuesIter.toList = m.values :=
  m.inner.valuesIter_toList

end Std.TreeMap
