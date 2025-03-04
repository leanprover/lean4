/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.DTreeMap.Internal.WF.Defs

/-!
# Dependent tree maps

This file develops the type `Std.DTreeMap` of dependent tree maps.

Lemmas about the operations on `Std.DTreeMap` will be available in the
module `Std.Data.DTreeMap.Lemmas`.

See the module `Std.Data.DTreeMap.Raw.Basic` for a variant of this type which is safe to use in
nested inductive types.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v w w₂

variable {α : Type u} {β : α → Type v} {cmp : α → α → Ordering}
private local instance : Coe (Type v) (α → Type v) where coe γ := fun _ => γ

namespace Std

/--
Dependent tree maps.

A tree map stores an assignment of keys to values. It depends on a comparator function that
defines an ordering on the keys and provides efficient order-dependent queries, such as retrieval
of the minimum or maximum.

To ensure that the operations behave as expected, the comparator function `cmp` should satisfy
certain laws that ensure a consistent ordering:

* If `a` is less than (or equal) to `b`, then `b` is greater than (or equal) to `a`
and vice versa (see the `OrientedCmp` typeclass).
* If `a` is less than or equal to `b` and `b` is, in turn, less than or equal to `c`, then `a`
is less than or equal to `c` (see the `TransCmp` typeclass).

Keys for which `cmp a b = Ordering.eq` are considered the same, i.e., there can be only one entry
with key either `a` or `b` in a tree map. Looking up either `a` or `b` always yields the same entry,
if any is present. The `get` operations of the _dependent_ tree map additionally require a
`LawfulEqCmp` instance to ensure that `cmp a b = .eq` always implies `a = b`, so that their
respective value types are equal.

To avoid expensive copies, users should make sure that the tree map is used linearly.

Internally, the tree maps are represented as size-bounded trees, a type of self-balancing binary
search tree with efficient order statistic lookups.

These tree maps contain a bundled well-formedness invariant, which means that they cannot
be used in nested inductive types. For these use cases, `Std.DTreeMap.Raw` and
`Std.DTreeMap.Raw.WF` unbundle the invariant from the tree map. When in doubt, prefer
`DTreeMap` over `DTreeMap.Raw`.
-/
structure DTreeMap (α : Type u) (β : α → Type v) (cmp : α → α → Ordering := by exact compare) where
  /-- Internal implementation detail of the tree map. -/
  inner : DTreeMap.Internal.Impl α β
  /-- Internal implementation detail of the tree map. -/
  wf : letI : Ord α := ⟨cmp⟩; inner.WF

namespace DTreeMap
open Internal (Impl)

/--
Creates a new empty tree map. It is also possible and recommended to
use the empty collection notations `∅` and `{}` to create an empty tree map. `simp` replaces
`empty` with `∅`.
-/
@[inline]
def empty : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Internal.Impl.empty, .empty⟩

instance : EmptyCollection (DTreeMap α β cmp) where
  emptyCollection := empty

instance : Inhabited (DTreeMap α β cmp) where
  default := ∅

@[simp]
theorem empty_eq_emptyc : (empty : DTreeMap α β cmp) = ∅ :=
  rfl

/--
Inserts the given mapping into the map. If there is already a mapping for the given key, then both
key and value will be replaced.
-/
@[inline]
def insert (t : DTreeMap α β cmp) (a : α) (b : β a) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨(t.inner.insert a b t.wf.balanced).impl, .insert t.wf⟩

instance : Singleton ((a : α) × β a) (DTreeMap α β cmp) where
  singleton e := (∅ : DTreeMap α β cmp).insert e.1 e.2

instance : Insert ((a : α) × β a) (DTreeMap α β cmp) where
  insert e s := s.insert e.1 e.2

instance : LawfulSingleton ((a : α) × β a) (DTreeMap α β cmp) where
  insert_emptyc_eq _ := rfl

/--
If there is no mapping for the given key, inserts the given mapping into the map. Otherwise,
returns the map unaltered.
-/
@[inline]
def insertIfNew (t : DTreeMap α β cmp) (a : α) (b : β a) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨(t.inner.insertIfNew a b t.wf.balanced).impl, t.wf.insertIfNew⟩

/--
Checks whether a key is present in a map and unconditionally inserts a value for the key.

Equivalent to (but potentially faster than) calling `contains` followed by `insert`.
-/
@[inline]
def containsThenInsert (t : DTreeMap α β cmp) (a : α) (b : β a) : Bool × DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsert a b t.wf.balanced
  (p.1, ⟨p.2.impl, t.wf.containsThenInsert⟩)

/--
Checks whether a key is present in a map and inserts a value for the key if it was not found.
If the returned `Bool` is `true`, then the returned map is unaltered. If the `Bool` is `false`,
then the returned map has a new value inserted.

Equivalent to (but potentially faster than) calling `contains` followed by `insertIfNew`.
-/
@[inline]
def containsThenInsertIfNew (t : DTreeMap α β cmp) (a : α) (b : β a) :
    Bool × DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsertIfNew a b t.wf.balanced
  (p.1, ⟨p.2.impl, t.wf.containsThenInsertIfNew⟩)

/--
Checks whether a key is present in a map, returning the associated value, and inserts a value for
the key if it was not found.

If the returned value is `some v`, then the returned map is unaltered. If it is `none`, then the
returned map has a new value inserted.

Equivalent to (but potentially faster than) calling `get?` followed by `insertIfNew`.

Uses the `LawfulEqCmp` instance to cast the retrieved value to the correct type.
-/
@[inline]
def getThenInsertIfNew? [LawfulEqCmp cmp] (t : DTreeMap α β cmp) (a : α) (b : β a) :
    Option (β a) × DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.getThenInsertIfNew? a b t.wf.balanced
  (p.1, ⟨p.2, t.wf.getThenInsertIfNew?⟩)

/--
Returns `true` if there is a mapping for the given key `a` or a key that is equal to `a` according
to the comparator `cmp`. There is also a `Prop`-valued version
of this: `a ∈ t` is equivalent to `t.contains a = true`.

Observe that this is different behavior than for lists: for lists, `∈` uses `=` and `contains` uses
`==` for equality checks, while for tree maps, both use the given comparator `cmp`.
-/
@[inline]
def contains (t : DTreeMap α β cmp) (a : α) : Bool :=
  letI : Ord α := ⟨cmp⟩; t.inner.contains a

instance : Membership α (DTreeMap α β cmp) where
  mem m a := m.contains a

instance {m : DTreeMap α β cmp} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs <| Decidable (m.contains a)

/-- Returns the number of mappings present in the map. -/
@[inline]
def size (t : DTreeMap α β cmp) : Nat :=
  t.inner.size

/-- Returns `true` if the tree map contains no mappings. -/
@[inline]
def isEmpty (t : DTreeMap α β cmp) : Bool :=
  t.inner.isEmpty

/-- Removes the mapping for the given key if it exists. -/
@[inline]
def erase (t : DTreeMap α β cmp) (a : α) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨(t.inner.erase a t.wf.balanced).impl, .erase t.wf⟩

/--
Tries to retrieve the mapping for the given key, returning `none` if no such mapping is present.

Uses the `LawfulEqCmp` instance to cast the retrieved value to the correct type.
-/
@[inline]
def get? [LawfulEqCmp cmp] (t : DTreeMap α β cmp) (a : α) : Option (β a) :=
  letI : Ord α := ⟨cmp⟩; t.inner.get? a

@[inline, inherit_doc get?, deprecated get? (since := "2025-02-12")]
def find? [LawfulEqCmp cmp] (t : DTreeMap α β cmp) (a : α) : Option (β a) :=
  t.get? a

/--
Given a proof that a mapping for the given key is present, retrieves the mapping for the given key.

Uses the `LawfulEqCmp` instance to cast the retrieved value to the correct type.
-/
@[inline]
def get [LawfulEqCmp cmp] (t : DTreeMap α β cmp) (a : α) (h : a ∈ t) : β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.get a h

/--
Tries to retrieve the mapping for the given key, panicking if no such mapping is present.

Uses the `LawfulEqCmp` instance to cast the retrieved value to the correct type.
-/
@[inline]
def get! [LawfulEqCmp cmp] (t : DTreeMap α β cmp) (a : α) [Inhabited (β a)]  : β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.get! a

@[inline, inherit_doc get!, deprecated get! (since := "2025-02-12")]
def find! [LawfulEqCmp cmp] (t : DTreeMap α β cmp) (a : α) [Inhabited (β a)]  : β a :=
  t.get! a

/--
Tries to retrieve the mapping for the given key, returning `fallback` if no such mapping is present.

Uses the `LawfulEqCmp` instance to cast the retrieved value to the correct type.
-/
@[inline]
def getD [LawfulEqCmp cmp] (t : DTreeMap α β cmp) (a : α) (fallback : β a) : β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.getD a fallback

@[inline, inherit_doc getD, deprecated getD (since := "2025-02-12")]
def findD [LawfulEqCmp cmp] (t : DTreeMap α β cmp) (a : α) (fallback : β a) : β a :=
  t.getD a fallback

/--
Checks if a mapping for the given key exists and returns the key if it does, otherwise `none`.
The result in the `some` case is guaranteed to be pointer equal to the key in the map.
-/
@[inline]
def getKey? (t : DTreeMap α β cmp) (a : α) : Option α :=
  letI : Ord α := ⟨cmp⟩; t.inner.getKey? a

/--
Retrieves the key from the mapping that matches `a`. Ensures that such a mapping exists by
requiring a proof of `a ∈ m`. The result is guaranteed to be pointer equal to the key in the map.
-/
@[inline]
def getKey (t : DTreeMap α β cmp) (a : α) (h : a ∈ t) : α :=
  letI : Ord α := ⟨cmp⟩; t.inner.getKey a h

/--
Checks if a mapping for the given key exists and returns the key if it does, otherwise panics.
If no panic occurs the result is guaranteed to be pointer equal to the key in the map.
-/
@[inline]
def getKey! [Inhabited α] (t : DTreeMap α β cmp) (a : α) : α :=
  letI : Ord α := ⟨cmp⟩; t.inner.getKey! a

/--
Checks if a mapping for the given key exists and returns the key if it does, otherwise `fallback`.
If a mapping exists the result is guaranteed to be pointer equal to the key in the map.
-/
@[inline]
def getKeyD (t : DTreeMap α β cmp) (a : α) (fallback : α) : α :=
  letI : Ord α := ⟨cmp⟩; t.inner.getKeyD a fallback

/--
Tries to retrieve the key-value pair with the smallest key in the tree map, returning `none` if the
map is empty.
-/
@[inline]
def min? (t : DTreeMap α β cmp) : Option ((a : α) × β a) :=
  letI : Ord α := ⟨cmp⟩; t.inner.min?

/--
Given a proof that the tree map is not empty, retrieves the key-value pair with the smallest key.
-/
@[inline]
def min (t : DTreeMap α β cmp) (h : t.isEmpty = false) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.min h

/--
Tries to retrieve the key-value pair with the smallest key in the tree map, panicking if the map is
empty.
-/
@[inline]
def min! [Inhabited ((a : α) × β a)] (t : DTreeMap α β cmp) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.min!

/--
Tries to retrieve the key-value pair with the smallest key in the tree map, returning `fallback` if
the tree map is empty.
-/
@[inline]
def minD (t : DTreeMap α β cmp) (fallback : (a : α) × β a) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.minD fallback

/--
Tries to retrieve the key-value pair with the largest key in the tree map, returning `none` if the
map is empty.
-/
@[inline]
def max? (t : DTreeMap α β cmp) : Option ((a : α) × β a) :=
  letI : Ord α := ⟨cmp⟩; t.inner.max?

/--
Given a proof that the tree map is not empty, retrieves the key-value pair with the largest key.
-/
@[inline]
def max (t : DTreeMap α β cmp) (h : t.isEmpty = false) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.max h

/--
Tries to retrieve the key-value pair with the largest key in the tree map, panicking if the map is
empty.
-/
@[inline]
def max! [Inhabited ((a : α) × β a)] (t : DTreeMap α β cmp) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.max!

/--
Tries to retrieve the key-value pair with the largest key in the tree map, returning `fallback` if
the tree map is empty.
-/
@[inline]
def maxD (t : DTreeMap α β cmp) (fallback : (a : α) × β a) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.maxD fallback

/--
Tries to retrieve the smallest key in the tree map, returning `none` if the map is empty.
-/
@[inline]
def minKey? (t : DTreeMap α β cmp) : Option α :=
  letI : Ord α := ⟨cmp⟩; t.inner.minKey?

/--
Given a proof that the tree map is not empty, retrieves the smallest key.
-/
@[inline]
def minKey (t : DTreeMap α β cmp) (h : t.isEmpty = false) : α :=
  letI : Ord α := ⟨cmp⟩; t.inner.minKey h

/--
Tries to retrieve the smallest key in the tree map, panicking if the map is empty.
-/
@[inline]
def minKey! [Inhabited α] (t : DTreeMap α β cmp) : α :=
  letI : Ord α := ⟨cmp⟩; t.inner.minKey!

/--
Tries to retrieve the smallest key in the tree map, returning `fallback` if the tree map is empty.
-/
@[inline]
def minKeyD (t : DTreeMap α β cmp) (fallback : α) : α :=
  letI : Ord α := ⟨cmp⟩; t.inner.minKeyD fallback

/--
Tries to retrieve the largest key in the tree map, returning `none` if the map is empty.
-/
@[inline]
def maxKey? (t : DTreeMap α β cmp) : Option α :=
  letI : Ord α := ⟨cmp⟩; t.inner.maxKey?

/--
Given a proof that the tree map is not empty, retrieves the largest key.
-/
@[inline]
def maxKey (t : DTreeMap α β cmp) (h : t.isEmpty = false) : α :=
  letI : Ord α := ⟨cmp⟩; t.inner.maxKey h

/--
Tries to retrieve the largest key in the tree map, panicking if the map is empty.
-/
@[inline]
def maxKey! [Inhabited α] (t : DTreeMap α β cmp) : α :=
  letI : Ord α := ⟨cmp⟩; t.inner.maxKey!

/--
Tries to retrieve the largest key in the tree map, returning `fallback` if the tree map is empty.
-/
@[inline]
def maxKeyD (t : DTreeMap α β cmp) (fallback : α) : α :=
  letI : Ord α := ⟨cmp⟩; t.inner.maxKeyD fallback

/-- Returns the key-value pair with the `n`-th smallest key, or `none` if `n` is at least `t.size`. -/
def entryAtIdx? (t : DTreeMap α β cmp) (n : Nat) : Option ((a : α) × β a) :=
  letI : Ord α := ⟨cmp⟩; t.inner.entryAtIdx? n

/-- Returns the key-value pair with the `n`-th smallest key. -/
def entryAtIdx (t : DTreeMap α β cmp) (n : Nat) (h : n < t.size) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; Impl.entryAtIdx t.inner t.wf.balanced n h

/-- Returns the key-value pair with the `n`-th smallest key, or panics if `n` is at least `t.size`. -/
def entryAtIdx! [Inhabited ((a : α) × β a)] (t : DTreeMap α β cmp) (n : Nat) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.entryAtIdx! n

/-- Returns the key-value pair with the `n`-th smallest key, or `fallback` if `n` is at least `t.size`. -/
def entryAtIdxD (t : DTreeMap α β cmp) (n : Nat)
    (fallback : (a : α) × β a) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.entryAtIdxD n fallback

/-- Returns the `n`-th smallest key, or `none` if `n` is at least `t.size`. -/
def keyAtIndex? (t : DTreeMap α β cmp) (n : Nat) : Option α :=
  letI : Ord α := ⟨cmp⟩; Impl.keyAtIndex? t.inner n

/-- Returns the `n`-th smallest key. -/
def keyAtIndex (t : DTreeMap α β cmp) (n : Nat) (h : n < t.size) : α :=
  letI : Ord α := ⟨cmp⟩; Impl.keyAtIndex t.inner t.wf.balanced n h

/-- Returns the `n`-th smallest key, or panics if `n` is at least `t.size`. -/
def keyAtIndex! [Inhabited α] (t : DTreeMap α β cmp) (n : Nat) : α :=
  letI : Ord α := ⟨cmp⟩; t.inner.keyAtIndex! n

/-- Returns the `n`-th smallest key, or `fallback` if `n` is at least `t.size`. -/
def keyAtIndexD (t : DTreeMap α β cmp) (n : Nat) (fallback : α) : α :=
  letI : Ord α := ⟨cmp⟩; t.inner.keyAtIndexD n fallback

/--
Tries to retrieve the key-value pair with the smallest key that is greater than or equal to the
given key, returning `none` if no such pair exists.
-/
@[inline]
def getEntryGE? (t : DTreeMap α β cmp) (k : α) : Option ((a : α) × β a) :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryGE? k t.inner

/--
Tries to retrieve the key-value pair with the smallest key that is greater than the given key,
returning `none` if no such pair exists.
-/
@[inline]
def getEntryGT? (t : DTreeMap α β cmp) (k : α) : Option ((a : α) × β a) :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryGT? k t.inner

/--
Tries to retrieve the key-value pair with the largest key that is less than or equal to the
given key, returning `none` if no such pair exists.
-/
@[inline]
def getEntryLE? (t : DTreeMap α β cmp) (k : α) : Option ((a : α) × β a) :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryLE? k t.inner

/--
Tries to retrieve the key-value pair with the smallest key that is less than the given key,
returning `none` if no such pair exists.
-/
@[inline]
def getEntryLT? (t : DTreeMap α β cmp) (k : α) : Option ((a : α) × β a) :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryLT? k t.inner

/-!
`getEntryGE`, `getEntryGT`, `getEntryLE`, `getEntryLT` can be found in
`Std.Data.DTreeMap.AdditionalOperations`.
-/

/--
Tries to retrieve the key-value pair with the smallest key that is greater than or equal to the
given key, panicking if no such pair exists.
-/
@[inline]
def getEntryGE! [Inhabited (Sigma β)] (t : DTreeMap α β cmp) (k : α) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryGE! k t.inner

/--
Tries to retrieve the key-value pair with the smallest key that is greater than the given key,
panicking if no such pair exists.
-/
@[inline]
def getEntryGT! [Inhabited (Sigma β)] (t : DTreeMap α β cmp) (k : α) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryGT! k t.inner

/--
Tries to retrieve the key-value pair with the largest key that is less than or equal to the
given key, panicking if no such pair exists.
-/
@[inline]
def getEntryLE! [Inhabited (Sigma β)] (t : DTreeMap α β cmp) (k : α) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryLE! k t.inner

/--
Tries to retrieve the key-value pair with the smallest key that is less than the given key,
panicking if no such pair exists.
-/
@[inline]
def getEntryLT! [Inhabited (Sigma β)] (t : DTreeMap α β cmp) (k : α) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryLT! k t.inner

/--
Tries to retrieve the key-value pair with the smallest key that is greater than or equal to the
given key, returning `fallback` if no such pair exists.
-/
@[inline]
def getEntryGED (t : DTreeMap α β cmp) (k : α) (fallback : Sigma β) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryGED k t.inner fallback

/--
Tries to retrieve the key-value pair with the smallest key that is greater than the given key,
returning `fallback` if no such pair exists.
-/
@[inline]
def getEntryGTD (t : DTreeMap α β cmp) (k : α) (fallback : Sigma β) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryGTD k t.inner fallback

/--
Tries to retrieve the key-value pair with the largest key that is less than or equal to the
given key, returning `fallback` if no such pair exists.
-/
@[inline]
def getEntryLED (t : DTreeMap α β cmp) (k : α) (fallback : Sigma β) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryLED k t.inner fallback

/--
Tries to retrieve the key-value pair with the smallest key that is less than the given key,
returning `fallback` if no such pair exists.
-/
@[inline]
def getEntryLTD (t : DTreeMap α β cmp) (k : α) (fallback : Sigma β) : (a : α) × β a :=
  letI : Ord α := ⟨cmp⟩; Impl.getEntryLTD k t.inner fallback

/--
Tries to retrieve the smallest key that is greater than or equal to the
given key, returning `none` if no such key exists.
-/
@[inline]
def getKeyGE? (t : DTreeMap α β cmp) (k : α) : Option α :=
  letI : Ord α := ⟨cmp⟩; t.inner.getKeyGE? k

/--
Tries to retrieve the smallest key that is greater than the given key,
returning `none` if no such key exists.
-/
@[inline]
def getKeyGT? (t : DTreeMap α β cmp) (k : α) : Option α :=
  letI : Ord α := ⟨cmp⟩; t.inner.getKeyGT? k

/--
Tries to retrieve the largest key that is less than or equal to the
given key, returning `none` if no such key exists.
-/
@[inline]
def getKeyLE? (t : DTreeMap α β cmp) (k : α) : Option α :=
  letI : Ord α := ⟨cmp⟩; t.inner.getKeyLE? k

/--
Tries to retrieve the smallest key that is less than the given key,
returning `none` if no such key exists.
-/
@[inline]
def getKeyLT? (t : DTreeMap α β cmp) (k : α) : Option α :=
  letI : Ord α := ⟨cmp⟩; t.inner.getKeyLT? k

/-!
`getKeyGE`, `getKeyGT`, `getKeyLE`, `getKeyLT` can be found in
`Std.Data.DTreeMap.AdditionalOperations`.
-/

/--
Tries to retrieve the smallest key that is greater than or equal to the
given key, panicking if no such key exists.
-/
@[inline]
def getKeyGE! [Inhabited α] (t : DTreeMap α β cmp) (k : α) : α :=
  letI : Ord α := ⟨cmp⟩; Impl.getKeyGE! k t.inner

/--
Tries to retrieve the smallest key that is greater than the given key,
panicking if no such key exists.
-/
@[inline]
def getKeyGT! [Inhabited α] (t : DTreeMap α β cmp) (k : α) : α :=
  letI : Ord α := ⟨cmp⟩; Impl.getKeyGT! k t.inner

/--
Tries to retrieve the largest key that is less than or equal to the
given key, panicking if no such key exists.
-/
@[inline]
def getKeyLE! [Inhabited α] (t : DTreeMap α β cmp) (k : α) : α :=
  letI : Ord α := ⟨cmp⟩; Impl.getKeyLE! k t.inner

/--
Tries to retrieve the smallest key that is less than the given key,
panicking if no such key exists.
-/
@[inline]
def getKeyLT! [Inhabited α] (t : DTreeMap α β cmp) (k : α) : α :=
  letI : Ord α := ⟨cmp⟩; Impl.getKeyLT! k t.inner

/--
Tries to retrieve the smallest key that is greater than or equal to the
given key, returning `fallback` if no such key exists.
-/
@[inline]
def getKeyGED (t : DTreeMap α β cmp) (k : α) (fallback : α) : α :=
  letI : Ord α := ⟨cmp⟩; Impl.getKeyGED k t.inner fallback

/--
Tries to retrieve the smallest key that is greater than the given key,
returning `fallback` if no such key exists.
-/
@[inline]
def getKeyGTD (t : DTreeMap α β cmp) (k : α) (fallback : α) : α :=
  letI : Ord α := ⟨cmp⟩; Impl.getKeyGTD k t.inner fallback

/--
Tries to retrieve the largest key that is less than or equal to the
given key, returning `fallback` if no such key exists.
-/
@[inline]
def getKeyLED (t : DTreeMap α β cmp) (k : α) (fallback : α) : α :=
  letI : Ord α := ⟨cmp⟩; Impl.getKeyLED k t.inner fallback

/--
Tries to retrieve the smallest key that is less than the given key,
returning `fallback` if no such key exists.
-/
@[inline]
def getKeyLTD (t : DTreeMap α β cmp) (k : α) (fallback : α) : α :=
  letI : Ord α := ⟨cmp⟩; Impl.getKeyLTD k t.inner fallback

namespace Const

variable {β : Type v}

@[inline, inherit_doc DTreeMap.getThenInsertIfNew?]
def getThenInsertIfNew? (t : DTreeMap α β cmp) (a : α) (b : β) :
    Option β × DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := Impl.Const.getThenInsertIfNew? t.inner a b t.wf.balanced
  (p.1, ⟨p.2, t.wf.constGetThenInsertIfNew?⟩)

@[inline, inherit_doc DTreeMap.get?]
def get? (t : DTreeMap α β cmp) (a : α) : Option β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.get? t.inner a

@[inline, inherit_doc get?, deprecated get? (since := "2025-02-12")]
def find? (t : DTreeMap α β cmp) (a : α) : Option β :=
  get? t a

@[inline, inherit_doc DTreeMap.get]
def get (t : DTreeMap α β cmp) (a : α) (h : a ∈ t) : β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.get t.inner a h

@[inline, inherit_doc DTreeMap.get!]
def get! (t : DTreeMap α β cmp) (a : α) [Inhabited β] : β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.get! t.inner a

@[inline, inherit_doc get!, deprecated get! (since := "2025-02-12")]
def find! (t : DTreeMap α β cmp) (a : α) [Inhabited β] : β :=
  get! t a

@[inline, inherit_doc DTreeMap.getD]
def getD (t : DTreeMap α β cmp) (a : α) (fallback : β) : β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getD t.inner a fallback

@[inline, inherit_doc getD, deprecated getD (since := "2025-02-12")]
def findD (t : DTreeMap α β cmp) (a : α) (fallback : β) : β :=
  getD t a fallback

@[inline, inherit_doc DTreeMap.min?]
def min? (t : DTreeMap α β cmp) : Option (α × β) :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.min? t.inner

@[inline, inherit_doc DTreeMap.min]
def min (t : DTreeMap α β cmp) (h : t.isEmpty = false) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.min t.inner h

@[inline, inherit_doc DTreeMap.min!]
def min! [Inhabited (α × β)] (t : DTreeMap α β cmp) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.min! t.inner

@[inline, inherit_doc DTreeMap.minD]
def minD (t : DTreeMap α β cmp) (fallback : α × β) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.minD t.inner fallback

@[inline, inherit_doc DTreeMap.max?]
def max? (t : DTreeMap α β cmp) : Option (α × β) :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.max? t.inner

@[inline, inherit_doc DTreeMap.max]
def max (t : DTreeMap α β cmp) (h : t.isEmpty = false) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.max t.inner h

@[inline, inherit_doc DTreeMap.max!]
def max! [Inhabited (α × β)] (t : DTreeMap α β cmp) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.max! t.inner

@[inline, inherit_doc DTreeMap.maxD]
def maxD (t : DTreeMap α β cmp) (fallback : α × β) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.maxD t.inner fallback

@[inline, inherit_doc DTreeMap.entryAtIdx?]
def entryAtIdx? (t : DTreeMap α β cmp) (n : Nat) : Option (α × β) :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.entryAtIdx? t.inner n

@[inline, inherit_doc DTreeMap.entryAtIdx]
def entryAtIdx (t : DTreeMap α β cmp) (n : Nat) (h : n < t.size) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.entryAtIdx t.inner t.wf.balanced n h

@[inline, inherit_doc DTreeMap.entryAtIdx!]
def entryAtIdx! [Inhabited (α × β)] (t : DTreeMap α β cmp) (n : Nat) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.entryAtIdx! t.inner n

@[inline, inherit_doc DTreeMap.entryAtIdxD]
def entryAtIdxD (t : DTreeMap α β cmp) (n : Nat)
    (fallback : α × β) : α × β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.entryAtIdxD t.inner n fallback

@[inline, inherit_doc DTreeMap.getEntryGE?]
def getEntryGE? (t : DTreeMap α β cmp) (k : α) : Option (α × β) :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryGE? k t.inner

@[inline, inherit_doc DTreeMap.getEntryGT?]
def getEntryGT? (t : DTreeMap α β cmp) (k : α) : Option (α × β) :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryGT? k t.inner

@[inline, inherit_doc DTreeMap.getEntryLE?]
def getEntryLE? (t : DTreeMap α β cmp) (k : α) : Option (α × β) :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryLE? k t.inner

@[inline, inherit_doc DTreeMap.getEntryLT?]
def getEntryLT? (t : DTreeMap α β cmp) (k : α) : Option (α × β) :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryLT? k t.inner

/-!
`getEntryGE`, `getEntryGT`, `getEntryLE`, `getEntryLT` can be found in
`Std.Data.DTreeMap.AdditionalOperations`.
-/

@[inline, inherit_doc DTreeMap.getEntryGE!]
def getEntryGE! [Inhabited (α × β)] (t : DTreeMap α β cmp) (k : α) : (α × β) :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryGE! k t.inner

@[inline, inherit_doc DTreeMap.getEntryGT!]
def getEntryGT! [Inhabited (α × β)] (t : DTreeMap α β cmp) (k : α) : (α × β) :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryGT! k t.inner

@[inline, inherit_doc DTreeMap.getEntryLE!]
def getEntryLE! [Inhabited (α × β)] (t : DTreeMap α β cmp) (k : α) : (α × β) :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryLE! k t.inner

@[inline, inherit_doc DTreeMap.getEntryLT!]
def getEntryLT! [Inhabited (α × β)] (t : DTreeMap α β cmp) (k : α) : (α × β) :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryLT! k t.inner

@[inline, inherit_doc DTreeMap.getEntryGED]
def getEntryGED (t : DTreeMap α β cmp) (k : α) (fallback : α × β) : (α × β) :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryGED k t.inner fallback

@[inline, inherit_doc DTreeMap.getEntryGTD]
def getEntryGTD (t : DTreeMap α β cmp) (k : α) (fallback : α × β) : (α × β) :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryGTD k t.inner fallback

@[inline, inherit_doc DTreeMap.getEntryLED]
def getEntryLED (t : DTreeMap α β cmp) (k : α) (fallback : α × β) : (α × β) :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryLED k t.inner fallback

@[inline, inherit_doc DTreeMap.getEntryLTD]
def getEntryLTD (t : DTreeMap α β cmp) (k : α) (fallback : α × β) : (α × β) :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getEntryLTD k t.inner fallback

end Const

variable {δ : Type w} {m : Type w → Type w₂} [Monad m]

/-- Removes all mappings of the map for which the given function returns `false`. -/
@[inline]
def filter (f : (a : α) → β a → Bool) (t : DTreeMap α β cmp) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.filter f t.wf.balanced |>.impl, t.wf.filter⟩

/-- Folds the given monadic function over the mappings in the map in ascending order. -/
@[inline]
def foldlM (f : δ → (a : α) → β a → m δ) (init : δ) (t : DTreeMap α β cmp) : m δ :=
  t.inner.foldlM f init

@[inline, inherit_doc foldlM, deprecated foldlM (since := "2025-02-12")]
def foldM (f : δ → (a : α) → β a → m δ) (init : δ) (t : DTreeMap α β cmp) : m δ :=
  t.foldlM f init

/-- Folds the given function over the mappings in the map in ascending order. -/
@[inline]
def foldl (f : δ → (a : α) → β a → δ) (init : δ) (t : DTreeMap α β cmp) : δ :=
  t.inner.foldl f init

@[inline, inherit_doc foldl, deprecated foldl (since := "2025-02-12")]
def fold (f : δ → (a : α) → β a → δ) (init : δ) (t : DTreeMap α β cmp) : δ :=
  t.foldl f init

/-- Folds the given monadic function over the mappings in the map in descending order. -/
@[inline]
def foldrM (f : (a : α) → β a → δ → m δ) (init : δ) (t : DTreeMap α β cmp) : m δ :=
  t.inner.foldrM f init

/-- Folds the given function over the mappings in the map in descending order. -/
@[inline]
def foldr (f : (a : α) → β a → δ → δ) (init : δ) (t : DTreeMap α β cmp) : δ :=
  t.inner.foldr f init

@[inline, inherit_doc foldr, deprecated foldr (since := "2025-02-12")]
def revFold (f : δ → (a : α) → β a → δ) (init : δ) (t : DTreeMap α β cmp) : δ :=
  foldr (fun k v acc => f acc k v) init t

/-- Partitions a tree map into two tree maps based on a predicate. -/
@[inline] def partition (f : (a : α) → β a → Bool)
    (t : DTreeMap α β cmp) : DTreeMap α β cmp × DTreeMap α β cmp :=
  t.foldl (init := (∅, ∅)) fun ⟨l, r⟩ a b =>
    if f a b then
      (l.insert a b, r)
    else
      (l, r.insert a b)

/-- Carries out a monadic action on each mapping in the tree map in ascending order. -/
@[inline]
def forM (f : (a : α) → β a → m PUnit) (t : DTreeMap α β cmp) : m PUnit :=
  t.inner.forM f

/-- Support for the `for` loop construct in `do` blocks. Iteration happens in ascending order. -/
@[inline]
def forIn (f : (a : α) → β a → δ → m (ForInStep δ)) (init : δ) (t : DTreeMap α β cmp) : m δ :=
  t.inner.forIn f init

instance : ForM m (DTreeMap α β cmp) ((a : α) × β a) where
  forM t f := t.forM (fun a b => f ⟨a, b⟩)

instance : ForIn m (DTreeMap α β cmp) ((a : α) × β a) where
  forIn m init f := m.forIn (fun a b acc => f ⟨a, b⟩ acc) init

namespace Const

variable {β : Type v}

/-!
We do not define `ForM` and `ForIn` instances that are specialized to constant `β`. Instead, we
define uncurried versions of `forM` and `forIn` that will be used in the `Const` lemmas and to
define the `ForM` and `ForIn` instances for `DTreeMap`.
-/

@[inline, inherit_doc DTreeMap.forM]
def forMUncurried (f : α × β → m PUnit) (t : DTreeMap α β cmp) : m PUnit :=
  t.inner.forM fun a b => f ⟨a, b⟩

@[inline, inherit_doc DTreeMap.forIn]
def forInUncurried (f : α × β → δ → m (ForInStep δ)) (init : δ) (t : DTreeMap α β cmp) : m δ :=
  t.inner.forIn (fun a b acc => f ⟨a, b⟩ acc) init

end Const

/-- Check if any element satisfes the predicate, short-circuiting if a predicate fails. -/
@[inline]
def any (t : DTreeMap α β cmp) (p : (a : α) → β a → Bool) : Bool := Id.run $ do
  for ⟨a, b⟩ in t do
    if p a b then return true
  return false

/-- Check if all elements satisfy the predicate, short-circuiting if a predicate fails. -/
@[inline]
def all (t : DTreeMap α β cmp) (p : (a : α) → β a → Bool) : Bool := Id.run $ do
  for ⟨a, b⟩ in t do
    if p a b = false then return false
  return true

/-- Returns a list of all keys present in the tree map in ascending  order. -/
@[inline]
def keys (t : DTreeMap α β cmp) : List α :=
  t.inner.keys

/-- Returns an array of all keys present in the tree map in ascending  order. -/
@[inline]
def keysArray (t : DTreeMap α β cmp) : Array α :=
  t.inner.keysArray

/-- Returns a list of all values present in the tree map in ascending  order. -/
@[inline]
def values {β : Type v} (t : DTreeMap α β cmp) : List β :=
  t.inner.values

/-- Returns an array of all values present in the tree map in ascending  order. -/
@[inline]
def valuesArray {β : Type v} (t : DTreeMap α β cmp) : Array β :=
  t.inner.valuesArray

/-- Transforms the tree map into a list of mappings in ascending order. -/
@[inline]
def toList (t : DTreeMap α β cmp) : List ((a : α) × β a) :=
  t.inner.toList

/-- Transforms a list of mappings into a tree map. -/
@[inline]
def ofList (l : List ((a : α) × β a)) (cmp : α → α → Ordering := by exact compare) :
    DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.ofList l, Impl.WF.empty.insertMany⟩

@[inline, inherit_doc ofList, deprecated ofList (since := "2025-02-12")]
def fromList (l : List ((a : α) × β a)) (cmp : α → α → Ordering) : DTreeMap α β cmp :=
  ofList l cmp

/-- Transforms the tree map into a list of mappings in ascending order. -/
@[inline]
def toArray (t : DTreeMap α β cmp) : Array ((a : α) × β a) :=
  t.inner.toArray

/-- Transforms an array of mappings into a tree map. -/
@[inline]
def ofArray (a : Array ((a : α) × β a)) (cmp : α → α → Ordering := by exact compare) :
    DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.ofArray a, Impl.WF.empty.insertMany⟩

@[inline, inherit_doc ofArray, deprecated ofArray (since := "2025-02-12")]
def fromArray (a : Array ((a : α) × β a)) (cmp : α → α → Ordering) : DTreeMap α β cmp :=
  ofArray a cmp

/--
Modifies in place the value associated with a given key.

This function ensures that the value is used linearly.
-/
@[inline]
def modify [LawfulEqCmp cmp] (t : DTreeMap α β cmp) (a : α) (f : β a → β a) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.modify a f, t.wf.modify⟩

/--
Modifies in place the value associated with a given key,
allowing creating new values and deleting values via an `Option` valued replacement function.

This function ensures that the value is used linearly.
-/
@[inline]
def alter [LawfulEqCmp cmp] (t : DTreeMap α β cmp) (a : α) (f : Option (β a) → Option (β a)) :
    DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.alter a f t.wf.balanced |>.impl, t.wf.alter⟩

/--
Returns a map that contains all mappings of `t₁` and `t₂`. In case that both maps contain the
same key `k` with respect to `cmp`, the provided function is used to determine the new value from
the respective values in `t₁` and `t₂`.

This function ensures that `t₁` is used linearly. It also uses the individual values in `t₁`
linearly if the merge function uses the second argument (i.e. the first of type `β a`) linearly.
Hence, as long as `t₁` is unshared, the performance characteristics follow the following imperative
description: Iterate over all mappings in `t₂`, inserting them into `t₁` if `t₁` does not contain a
conflicting mapping yet. If `t₁` does contain a conflicting mapping, use the given merge function to
merge the mapping in `t₂` into the mapping in `t₁`. Then return `t₁`.

Hence, the runtime of this method scales logarithmically in the size of `t₁` and linearly in the size of
`t₂` as long as `t₁` is unshared.
-/
@[inline]
def mergeWith [LawfulEqCmp cmp] (mergeFn : (a : α) → β a → β a → β a) (t₁ t₂ : DTreeMap α β cmp) :
    DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t₁.inner.mergeWith mergeFn t₂.inner t₁.wf.balanced |>.impl, t₁.wf.mergeWith⟩

@[inline, inherit_doc mergeWith, deprecated mergeWith (since := "2025-02-12")]
def mergeBy [LawfulEqCmp cmp] (mergeFn : (a : α) → β a → β a → β a) (t₁ t₂ : DTreeMap α β cmp) :
    DTreeMap α β cmp :=
  mergeWith mergeFn t₁ t₂

namespace Const

variable {β : Type v}

@[inline, inherit_doc DTreeMap.toList]
def toList (t : DTreeMap α β cmp) : List (α × β) :=
  Impl.Const.toList t.inner

@[inline, inherit_doc DTreeMap.ofList]
def ofList (l : List (α × β)) (cmp : α → α → Ordering := by exact compare) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩
  ⟨Impl.Const.ofList l, Impl.WF.empty.constInsertMany⟩

@[inline, inherit_doc DTreeMap.toArray]
def toArray (t : DTreeMap α β cmp) : Array (α × β) :=
  t.foldl (init := ∅) fun acc k v => acc.push ⟨k,v⟩

@[inline, inherit_doc DTreeMap.ofList]
def ofArray (a : Array (α × β)) (cmp : α → α → Ordering := by exact compare) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩
  ⟨Impl.Const.ofArray a, Impl.WF.empty.constInsertMany⟩

/-- Transforms a list of keys into a tree map. -/
@[inline]
def unitOfList (l : List α) (cmp : α → α → Ordering := by exact compare) : DTreeMap α Unit cmp :=
  letI : Ord α := ⟨cmp⟩
  ⟨Impl.Const.unitOfList l, Impl.WF.empty.constInsertManyIfNewUnit⟩

/-- Transforms an array of keys into a tree map. -/
@[inline]
def unitOfArray (a : Array α) (cmp : α → α → Ordering := by exact compare) : DTreeMap α Unit cmp :=
  letI : Ord α := ⟨cmp⟩
  ⟨Impl.Const.unitOfArray a, Impl.WF.empty.constInsertManyIfNewUnit⟩

@[inline, inherit_doc DTreeMap.modify]
def modify (t : DTreeMap α β cmp) (a : α) (f : β → β) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.modify a f t.inner, t.wf.constModify⟩

@[inline, inherit_doc DTreeMap.alter]
def alter (t : DTreeMap α β cmp) (a : α) (f : Option β → Option β) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.alter a f t.inner t.wf.balanced |>.impl, t.wf.constAlter⟩

@[inline, inherit_doc DTreeMap.mergeWith]
def mergeWith (mergeFn : α → β → β → β) (t₁ t₂ : DTreeMap α β cmp) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩;
  ⟨Impl.Const.mergeWith mergeFn t₁.inner t₂.inner t₁.wf.balanced |>.impl, t₁.wf.constMergeWith⟩

@[inline, inherit_doc mergeWith, deprecated mergeWith (since := "2025-02-12")]
def mergeBy (mergeFn : α → β → β → β) (t₁ t₂ : DTreeMap α β cmp) : DTreeMap α β cmp :=
  mergeWith mergeFn t₁ t₂

end Const

/--
Inserts multiple mappings into the tree map by iterating over the given collection and calling
`insert`. If the same key appears multiple times, the last occurrence takes precedence.

Note: this precedence behavior is true for `TreeMap`, `DTreeMap`, `TreeMap.Raw` and `DTreeMap.Raw`.
The `insertMany` function on `TreeSet` and `TreeSet.Raw` behaves differently: it will prefer the first
appearance.
-/
@[inline]
def insertMany {ρ} [ForIn Id ρ ((a : α) × β a)] (t : DTreeMap α β cmp) (l : ρ) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.insertMany l t.wf.balanced, t.wf.insertMany⟩

/--
Erases multiple mappings from the tree map by iterating over the given collection and calling
`erase`.
-/
@[inline]
def eraseMany {ρ} [ForIn Id ρ α] (t : DTreeMap α β cmp) (l : ρ) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.eraseMany l t.wf.balanced, t.wf.eraseMany⟩

namespace Const

variable {β : Type v}

@[inline, inherit_doc DTreeMap.insertMany]
def insertMany {ρ} [ForIn Id ρ (α × β)] (t : DTreeMap α β cmp) (l : ρ) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.insertMany t.inner l t.wf.balanced, t.wf.constInsertMany⟩

/--
Inserts multiple elements into the tree map by iterating over the given collection and calling
`insertIfNew`. If the same key appears multiple times, the first occurrence takes precedence.
-/
@[inline]
def insertManyIfNewUnit {ρ} [ForIn Id ρ α] (t : DTreeMap α Unit cmp) (l : ρ) : DTreeMap α Unit cmp :=
  letI : Ord α := ⟨cmp⟩;
  ⟨Impl.Const.insertManyIfNewUnit t.inner l t.wf.balanced, t.wf.constInsertManyIfNewUnit⟩

end Const

instance [Repr α] [(a : α) → Repr (β a)] : Repr (DTreeMap α β cmp) where
  reprPrec m prec := Repr.addAppParen ("DTreeMap.ofList " ++ repr m.toList) prec

end DTreeMap

end Std
