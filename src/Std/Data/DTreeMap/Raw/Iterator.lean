/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.DTreeMap.Internal.Zipper
public import Std.Data.DTreeMap.Raw.Basic
import Init.Data.Iterators.Lemmas.Combinators.FilterMap

/-!
# Iterators on `DTreeMap.Raw`
-/

namespace Std.DTreeMap.Raw
open Std.Iterators

/--
Returns a finite iterator over the entries of a dependent tree map.
The iterator yields the elements of the map in order and then terminates.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
public def iter {α : Type u} {β : α → Type v}
    {cmp : α → α → Ordering} (m : Raw α β cmp) :=
  (Internal.Zipper.iterOfTree m.inner : Iter ((a : α) × β a))

/--
Returns a finite iterator over the keys of a dependent tree map.
The iterator yields the keys in order and then terminates.

The key and value types must live in the same universe.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
public def keysIter {α : Type u} {β : α → Type u}
    {cmp : α → α → Ordering} (m : Raw α β cmp) :=
  (m.iter.map fun e => e.1 : Iter α)

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
    {cmp : α → α → Ordering} (m : Raw α (fun _ => β) cmp) :=
  (m.iter.map fun e => e.2 : Iter β)

@[simp]
public theorem toList_iter {cmp : α → α → Ordering} (m : Raw α β cmp) :
    (m.iter).toList = m.toList := by
  rw [iter, toList]
  apply Internal.Zipper.toList_iterOfTree

@[simp]
public theorem keysIter_toList {cmp : α → α → Ordering} (m : Raw α β cmp) :
    (m.keysIter).toList = m.keys := by
  rw [keysIter, keys, iter, ← Internal.Impl.map_fst_toList_eq_keys]
  rw [Iter.toList_map, Internal.Zipper.toList_iterOfTree]

@[simp]
public theorem valuesIter_toList {cmp : α → α → Ordering} (m : Raw α (fun _ => β) cmp) :
    (m.valuesIter).toList = m.values := by
  rw [valuesIter, values, iter, Internal.Impl.values_eq_map_snd, ← Internal.Impl.toList_eq_toListModel]
  rw [Iter.toList_map, Internal.Zipper.toList_iterOfTree]

end Std.DTreeMap.Raw
