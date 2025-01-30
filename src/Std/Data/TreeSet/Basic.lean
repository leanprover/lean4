/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.TreeMap.Basic
import Std.Data.TreeSet.Raw

/-!
# Tree sets

This file develops the type `Std.Data.TreeSet` of tree sets.

Lemmas about the operations on `Std.Data.TreeSet` are available in the
module `Std.Data.TreeSet.Lemmas`.

See the module `Std.Data.TreeSet.Raw` for a variant of this type which is safe to use in
nested inductive types.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v

variable {α : Type u} {cmp : α → α → Ordering}

namespace Std

/--
Tree sets.

A tree set stores elements of a certain type in a certain order. It depends on a comparator function
that defines an ordering on the keys and provides efficient order-dependent queries, such as
retrieval of the minimum or maximum.

To ensure that the operations behave as expected, the comparator function `cmp` should satisfy
certain laws that ensure a consistent ordering:

* If `a` is less than (or equal) to `b`, then `b` is greater than (or equal) to `a`
and vice versa (see the `OrientedCmp` typeclass)
* If `a` is less than or equal to `b` and `b` is, in turn, less than or equal to `c`, then `a`
id less than or equal to `c` (see the `TransCmp` typeclass).

Keys for which `cmp a b = Ordering.eq` are considered the same, i.e there can be only one of them
be contained in a single tree set at the same time.

To avoid expensive copies, users should make sure that the tree set is used linearly to avoid
expensive copies.

Internally, the tree sets are represented as weight-balanced trees.

These tree sets contain a bundled well-formedness invariant, which means that they cannot
be used in nested inductive types. For these use cases, `Std.Data.TreeSet.Raw` and
`Std.Data.TreeSet.Raw.WF` unbundle the invariant from the tree set. When in doubt, prefer
`TreeSet` over `TreeSet.Raw`.
-/
structure TreeSet (α : Type u) (cmp : α → α → Ordering) where
  /-- Internal implementation detail of the tree map. -/
  inner : TreeMap α Unit cmp

namespace TreeSet

@[inline, inherit_doc Raw.empty]
def empty : TreeSet α cmp :=
  ⟨TreeMap.empty⟩

instance : EmptyCollection (TreeSet α cmp) where
  emptyCollection := empty

@[inline, inherit_doc Raw.isEmpty]
def isEmpty (t : TreeSet α cmp) : Bool :=
  t.inner.isEmpty

@[inline, inherit_doc Raw.insert]
def insert (l : TreeSet α cmp) (a : α) : TreeSet α cmp :=
  ⟨l.inner.insert a ()⟩

@[inline, inherit_doc Raw.contains]
def contains (l : TreeSet α cmp) (a : α) : Bool :=
  l.inner.contains a

@[inline, inherit_doc Raw.size]
def size (t : TreeSet α cmp) : Nat :=
  t.inner.size

@[inline, inherit_doc Raw.erase]
def erase (t : TreeSet α cmp) (a : α) : TreeSet α cmp :=
  ⟨t.inner.erase a⟩

@[inline, inherit_doc Raw.containsThenInsert]
def containsThenInsert (t : TreeSet α cmp) (a : α) : Bool × TreeSet α cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsert a ()
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc Raw.insertIfNew]
def insertIfNew (t : TreeSet α cmp) (a : α) : TreeSet α cmp :=
  ⟨t.inner.insertIfNew a ()⟩

@[inline, inherit_doc Raw.containsThenInsertIfNew]
def containsThenInsertIfNew (t : TreeSet α cmp) (a : α) :
    Bool × TreeSet α cmp :=
  let p := t.inner.containsThenInsertIfNew a ()
  (p.1, ⟨p.2⟩)

instance : Membership α (TreeSet α cmp) where
  mem m a := m.contains a

instance {m : TreeSet α cmp} {a : α} : Decidable (a ∈ m) :=
  show Decidable (m.contains a) from inferInstance

end TreeSet

end Std
