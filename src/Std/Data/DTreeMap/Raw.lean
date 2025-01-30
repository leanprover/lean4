/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DTreeMap.Internal.Impl

/-
# Dependent tree maps with unbundled well-formedness invariant

This file develops the type `Std.Data.DTreeMap.Raw` of dependent tree maps with unbundled
well-formedness invariant.

This version is safe to use in nested inductive types. The well-formedness predicate is
available as `Std.Data.DTreeMap.Raw.WF` and we prove in this file that all operations preserve
well-formedness. When in doubt, prefer `DTreeMap` over `DTreeMap.Raw`.

Lemmas about the operations on `Std.Data.DTreeMap.Raw` are available in the module
`Std.Data.DTreeMap.RawLemmas`.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v

variable {α : Type u} {β : α → Type v} {cmp : α → α → Ordering}

namespace Std

namespace DTreeMap

/--
Dependent tree maps without a bundled well-formedness invariant, suitable for use in nested
inductive types. The well-formedness invariant is called `Raw.WF`. When in doubt, prefer `DTreeMap`
over `DTreeMap.Raw`. Lemmas about the operations on `Std.Data.DTreeMap.Raw` are available in the
module `Std.Data.DTreeMap.RawLemmas`.

A tree map stores an assignment of keys to values. It depends on a comparator function that
defines an ordering on the keys and provides efficient order-dependent queries, such as retrieval
of the minimum or maximum.

To ensure that the operations behave as expected, the comparator function `cmp` should satisfy
certain laws that ensure a consistent ordering:

* If `a` is less than (or equal) to `b`, then `b` is greater than (or equal) to `a`
and vice versa (see the `OrientedCmp` typeclass)
* If `a` is less than or equal to `b` and `b` is, in turn, less than or equal to `c`, then `a`
id less than or equal to `c` (see the `TransCmp` typeclass).

Keys for which `cmp a b = Ordering.eq` are considered the same, i.e there can be only one entry
with key either `a` or `b` in a tree map. Looking up either `a` or `b` always yield the same entry,
if any is present. The `get` operations of the _dependent_ tree map additionally require a
`LawfulEqOrd` instance to ensure that `cmp a b = .eq` always implies `a = b`, and therefore their
respective value types are equal.

To avoid expensive copies, users should make sure that the tree map is used linearly to avoid
expensive copies.

Internally, the tree maps are represented as weight-balanced trees.

These tree maps contain a bundled well-formedness invariant, which means that they cannot
be used in nested inductive types. For these use cases, `Std.Data.DTreeMap.Raw` and
`Std.Data.DTreeMap.Raw.WF` unbundle the invariant from the tree map. When in doubt, prefer
`DTreeMap` over `DTreeMap.Raw`.
-/
structure Raw (α : Type u) (β : α → Type v) (_cmp : α → α → Ordering) where
  /-- Internal implementation detail of the tree map. -/
  inner : Internal.Impl α β

namespace Raw

/--
Well-formedness predicate for tree maps. Users of `DTreeMap` will not need to interact with
this. Users of `DTreeMap.Raw` will need to provide proofs of `WF` to lemmas and should use lemmas
like `WF.empty` and `WF.insert` (which are always named exactly like the operations they are about)
to show that map operations preserve well-formedness. The constructors of this type are internal
implementation details and should not be accessed by users.
-/
structure WF (t : Raw α β cmp) where
  /-- Internal implementation detail of the tree map. -/
  out : letI : Ord α := ⟨cmp⟩; t.inner.WF

instance {t : Raw α β cmp} : Coe t.WF (letI : Ord α := ⟨cmp⟩; t.inner.WF) where
  coe h := h.out

/--
Creates a new empty tree map. It is also possible to
use the empty collection notations `∅` and `{}` to create an empty tree map.
-/
@[inline]
def empty : Raw α β cmp :=
  ⟨Internal.Impl.empty⟩

instance : EmptyCollection (Raw α β cmp) where
  emptyCollection := empty

/--
Returns `true` if the tree map contains no mappings.
-/
@[inline]
def isEmpty (t : Raw α β cmp) : Bool :=
  t.inner.isEmpty

/--
Inserts the given mapping into the map. If there is already a mapping for the given key, then both
key and value will be replaced.
-/
@[inline]
def insert (l : Raw α β cmp) (a : α) (b : β a) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨l.inner.insertSlow a b⟩

/--
Inserts the given mapping into the map. If there is already a mapping for the given key, then both
key and value will be replaced.
-/
@[inline]
def insertFast (l : Raw α β cmp) (h : l.WF) (a : α) (b : β a) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨(l.inner.insert a b h.out.balanced).impl⟩

/--
Returns `true` if there is a mapping for the given key `a` or a key that is equal to `a` according
to the comparator `cmp`. There is also a `Prop`-valued version
of this: `a ∈ t` is equivalent to `t.contains a = true`.

Observe that this is different behavior than for lists: for lists, `∈` uses `=` and `contains` uses
`==` for equality checks, while for tree maps, both use the given comparator `cmp`.
-/
@[inline]
def contains (l : Raw α β cmp) (a : α) : Bool :=
  letI : Ord α := ⟨cmp⟩; l.inner.contains a

/-- Returns the number of mappings present in the map. -/
@[inline]
def size (t : Raw α β cmp) : Nat :=
  letI : Ord α := ⟨cmp⟩; t.inner.size

/-- Removes the mapping for the given key if it exists. -/
@[inline]
def erase (l : Raw α β cmp) (a : α) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨l.inner.eraseSlow a⟩

/--
Checks whether a key is present in a map and inserts a value for the key if it was not found.

If the returned `Bool` is `true`, then the returned map is unaltered. If the `Bool` is `false`, then
the returned map has a new value inserted.

Equivalent to (but potentially faster than) calling `contains` followed by `insertIfNew`.
-/
@[inline]
def containsThenInsert (t : Raw α β cmp) (a : α) (b : β a) : Bool × Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsertSlow a b
  (p.1, ⟨p.2⟩)

/--
If there is no mapping for the given key, inserts the given mapping into the map. Otherwise,
returns the map unaltered.
-/
@[inline] def insertIfNew (t : Raw α β cmp) (a : α) (b : β a) : Raw α β cmp :=
    letI : Ord α := ⟨cmp⟩; ⟨t.inner.insertIfNewSlow a b⟩

/--
Checks whether a key is present in a map and inserts a value for the key if it was not found.

If the returned `Bool` is `true`, then the returned map is unaltered. If the `Bool` is `false`, then
the returned map has a new value inserted.

Equivalent to (but potentially faster than) calling `contains` followed by `insertIfNew`.
-/
@[inline] def containsThenInsertIfNew (t : Raw α β cmp) (a : α) (b : β a) :
    Bool × Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsertIfNewSlow a b
  (p.1, ⟨p.2⟩)

instance : Membership α (Raw α β cmp) where
  mem m a := m.contains a

instance {m : Raw α β cmp} {a : α} : Decidable (a ∈ m) :=
  show Decidable (m.contains a) from inferInstance

end Raw

end DTreeMap

end Std
