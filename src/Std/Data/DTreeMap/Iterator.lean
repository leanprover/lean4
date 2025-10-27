/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module

prelude
public import Std.Data.DTreeMap.Raw.Iterator

/-!
# Iterators on `DTreeMap`
-/

namespace Std.DTreeMap
open Std.Iterators

/--
Returns a finite iterator over the entries of a dependent tree map.
The iterator yields the elements of the map in order and then terminates.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
public def iter {α : Type u} {β : α → Type v} [Ord α] (m : DTreeMap α β) :=
  Raw.iter ⟨m.inner⟩

/--
Returns a finite iterator over the keys of a dependent tree map.
The iterator yields the keys in order and then terminates.

The key and value types must live in the same universe.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
public def keysIter {α : Type u} {β : α → Type u} [Ord α] (m : Raw α β) :=
  Raw.keysIter ⟨m.inner⟩

/--
Returns a finite iterator over the values of a tree map.
The iterator yields the values in order and then terminates.

The key and value types must live in the same universe.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
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
