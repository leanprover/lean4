/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.TreeMap.Raw

/-
# Tree sets with unbundled well-formedness invariant

This file develops the type `Std.Data.TreeSet.Raw` of tree sets with unbundled
well-formedness invariant.

This version is safe to use in nested inductive types. The well-formedness predicate is
available as `Std.Data.TreeSet.Raw.WF` and we prove in this file that all operations preserve
well-formedness. When in doubt, prefer `TreeSet` over `TreeSet.Raw`.

Lemmas about the operations on `Std.Data.TreeSet.Raw` are available in the module
`Std.Data.TreeSet.RawLemmas`.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v

variable {α : Type u} {cmp : α → α → Ordering}

namespace Std

namespace TreeSet

/--
Tree sets without a bundled well-formedness invariant, suitable for use in nested
inductive types. The well-formedness invariant is called `Raw.WF`. When in doubt, prefer `TreeSet`
over `TreeSet.Raw`. Lemmas about the operations on `Std.Data.TreeSet.Raw` are available in the
module `Std.Data.TreeSet.RawLemmas`.

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

To avoid expensive copies, users should make sure that the tree map is used linearly to avoid
expensive copies.

Internally, the tree sets are represented as weight-balanced trees.
-/
structure Raw (α : Type u) (cmp : α → α → Ordering) where
  /-- Internal implementation detail of the tree map. -/
  inner : TreeMap.Raw α Unit cmp

namespace Raw

/--
Well-formedness predicate for tree sets. Users of `TreeSet` will not need to interact with
this. Users of `TreeSet.Raw` will need to provide proofs of `WF` to lemmas and should use lemmas
like `WF.empty` and `WF.insert` (which are always named exactly like the operations they are about)
to show that set operations preserve well-formedness. The constructors of this type are internal
implementation details and should not be accessed by users.
-/
structure WF (t : Raw α cmp) where
  /-- Internal implementation detail of the tree map. -/
  out : t.inner.WF

instance {t : Raw α cmp} : Coe t.WF t.inner.WF where
  coe t := t.out

/--
Creates a new empty tree set. It is also possible to
use the empty collection notations `∅` and `{}` to create an empty tree set.
-/
@[inline]
def empty : Raw α cmp :=
  ⟨TreeMap.Raw.empty⟩

instance : EmptyCollection (Raw α cmp) where
  emptyCollection := empty

/--
Returns `true` if the tree set contains no mappings.
-/
@[inline]
def isEmpty (t : Raw α cmp) : Bool :=
  t.inner.isEmpty

/--
Inserts the given element into the set. If `a` or an element that is equal according to the
comparator `cmp`, then the existing element will be replaced.
-/
@[inline]
def insert (l : Raw α cmp) (a : α) : Raw α cmp :=
  ⟨l.inner.insert a ()⟩

/--
Inserts the given element into the set. If `a` or an element that is equal according to the
comparator `cmp`, then the existing element will be replaced.
-/
@[inline]
def insertFast (l : Raw α cmp) (h : l.WF) (a : α) : Raw α cmp :=
  ⟨l.inner.insertFast h.out a ()⟩

/--
Returns `true` if `a`, or an element equal to `a` according to the comparator `cmp`, is contained
in the set. There is also a `Prop`-valued version of this: `a ∈ t` is equivalent to
`t.contains a = true`.

Observe that this is different behavior than for lists: for lists, `∈` uses `=` and `contains` uses
`==` for equality checks, while for tree sets, both use the given comparator `cmp`.
-/
@[inline]
def contains (l : Raw α cmp) (a : α) : Bool :=
  l.inner.contains a

/-- Returns the number of mappings present in the map. -/
@[inline]
def size (t : Raw α cmp) : Nat :=
  t.inner.size

/-- Removes the given key if it exists. -/
@[inline]
def erase (t : Raw α cmp) (a : α) : Raw α cmp :=
  ⟨t.inner.erase a⟩

/--
Checks whether an element is present in a set and inserts the element if it was not found.
If the hash set already contains an element that is equal (with regard to `cmp`) to the given
element, then the hash set is returned unchanged.

Equivalent to (but potentially faster than) calling `contains` followed by `insert`.
-/
@[inline]
def containsThenInsert (t : Raw α cmp) (a : α) : Bool × Raw α cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsert a ()
  (p.1, ⟨p.2⟩)

/--
Inserts the given element into the set. If the tree set already contains an element that is
equal (with regard to `==`) to the given element, then the tree set is returned unchanged.

Note: this non-replacement behavior is true for `TreeSet` and `TreeSet.Raw`.
The `insert` function on `TreeMap`, `DTreeMap`, `TreeMap.Raw` and `DTreeMap.Raw` behaves
differently: it will overwrite an existing mapping.
-/
@[inline]
def insertIfNew (t : Raw α cmp) (a : α) : Raw α cmp :=
    letI : Ord α := ⟨cmp⟩; ⟨t.inner.insertIfNew a ()⟩

/--
Checks whether an element is present in a set and inserts the element if it was not found.
If the hash set already contains an element that is equal (with regard to `==`) to the given
element, then the hash set is returned unchanged.

Equivalent to (but potentially faster than) calling `contains` followed by `insert`.
-/
@[inline]
def containsThenInsertIfNew (t : Raw α cmp) (a : α) :
    Bool × Raw α cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsertIfNew a ()
  (p.1, ⟨p.2⟩)

instance : Membership α (Raw α cmp) where
  mem m a := m.contains a

instance {m : Raw α cmp} {a : α} : Decidable (a ∈ m) :=
  show Decidable (m.contains a) from inferInstance

end Raw

end TreeSet

end Std
