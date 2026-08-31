/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.TreeSet.Raw.Basic
public import Std.Data.TreeMap.Raw.Iterator
public import Std.Data.DTreeMap.Raw.Lemmas
import Init.Data.Iterators.Lemmas.Combinators.FilterMap

/-!
# Iterators on `DTreeMap`
-/

namespace Std.TreeSet.Raw
open Std.Iterators

/--
Returns a finite iterator over the entries of a tree set.
The iterator yields the elements of the set in order and then terminates.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
public def iter {α : Type u}
    {cmp : α → α → Ordering} (m : Raw α cmp) :=
  (m.inner.iter.map fun e => e.1 : Iter α)

@[simp]
public theorem toList_iter {cmp : α → α → Ordering} (m : Raw α cmp) :
    m.iter.toList = m.toList := by
  rw [iter, Iter.toList_map, TreeMap.Raw.toList_iter, TreeMap.Raw.toList]
  rw [TreeSet.Raw.toList]
  rw [Std.DTreeMap.Internal.Impl.foldr_eq_foldr_toList]
  simp only [DTreeMap.Raw.Const.map_fst_toList_eq_keys, List.empty_eq, List.foldr_cons_eq_append,
    List.append_nil]
  rw [DTreeMap.Raw.keys, ← Std.DTreeMap.Internal.Impl.map_fst_toList_eq_keys]

end Std.TreeSet.Raw
