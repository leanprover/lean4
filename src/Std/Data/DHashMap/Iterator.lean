/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Std.Data.Iterators.Producers.Array
public import Init.Data.Iterators.Combinators.FlatMap
public import Std.Data.DHashMap.Basic
public import Std.Data.DHashMap.Internal.AssocList.Iterator
import Init.Data.Iterators.Combinators.FilterMap

/-!
# Iterators on `DHashMap` and `DHashMap.Raw`
-/

namespace Std.DHashMap.Raw

/--
Returns a finite iterator over the entries of a dependent hash map.
The iterator yields the elements of the map in order and then terminates.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
public def iter {α : Type u} {β : α → Type v} (m : Raw α β) :=
  (m.buckets.iter.flatMap fun b => b.iter : Iter ((a : α) × β a))

/--
Returns a finite iterator over the keys of a dependent hash map.
The iterator yields the keys in order and then terminates.

The key and value types must live in the same universe.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
public def keysIter {α : Type u} {β : α → Type u} (m : Raw α β) :=
  (m.iter.map fun e => e.1 : Iter α)

/--
Returns a finite iterator over the values of a hash map.
The iterator yields the values in order and then terminates.

The key and value types must live in the same universe.

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always
-/
@[inline]
public def valuesIter {α : Type u} {β : Type u} (m : Raw α (fun _ => β)) :=
  (m.iter.map fun e => e.2 : Iter β)

end Std.DHashMap.Raw

namespace Std.DHashMap

@[inline, inherit_doc Raw.iter]
public def iter {α : Type u} {β : α → Type v} [BEq α] [Hashable α] (m : DHashMap α β) :=
  (m.1.iter : Iter ((a : α) × β a))

@[inline, inherit_doc Raw.keysIter]
public def keysIter {α : Type u} {β : α → Type u} [BEq α] [Hashable α] (m : DHashMap α β) :=
  (m.1.keysIter : Iter α)

@[inline, inherit_doc Raw.valuesIter]
public def valuesIter {α : Type u} {β : Type u} [BEq α] [Hashable α]
    (m : DHashMap α (fun _ => β)) :=
  (m.iter.map fun e => e.2 : Iter β)

end Std.DHashMap
