/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DTreeMap.Internal.Impl
import Std.Data.DTreeMap.Raw

/-!
# Dependent tree maps

This file develops the type `Std.Data.DTreeMap` of dependent tree maps.

Lemmas about the operations on `Std.Data.DTreeMap` are available in the
module `Std.Data.DTreeMap.Lemmas`.

See the module `Std.Data.DTreeMap.Raw` for a variant of this type which is safe to use in
nested inductive types.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v

variable {α : Type u} {β : α → Type v} {cmp : α → α → Ordering}

namespace Std

/--
Dependent tree maps.

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
structure DTreeMap (α : Type u) (β : α → Type v) (cmp : α → α → Ordering) where
  /-- Internal implementation detail of the tree map. -/
  inner : DTreeMap.Internal.Impl α β
  /-- Internal implementation detail of the tree map. -/
  wf : letI : Ord α := ⟨cmp⟩; inner.WF

namespace DTreeMap

@[inline, inherit_doc Raw.isEmpty]
def isEmpty (t : DTreeMap α β cmp) : Bool :=
  t.inner.isEmpty

@[inline, inherit_doc Raw.empty]
def empty : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Internal.Impl.empty, .empty⟩

@[inline, inherit_doc Raw.insert]
def insert (l : DTreeMap α β cmp) (a : α) (b : β a) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨(l.inner.insert a b l.wf.balanced).impl, .insert l.wf⟩

@[inline, inherit_doc Raw.contains]
def contains (l : DTreeMap α β cmp) (a : α) : Bool :=
  letI : Ord α := ⟨cmp⟩; l.inner.contains a

@[inline, inherit_doc Raw.size]
def size (t : DTreeMap α β cmp) : Nat :=
  letI : Ord α := ⟨cmp⟩; t.inner.size

@[inline, inherit_doc Raw.erase]
def erase (l : DTreeMap α β cmp) (a : α) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨(l.inner.erase a l.wf.balanced).impl, .erase l.wf⟩

instance : Membership α (DTreeMap α β cmp) where
  mem m a := m.contains a

end DTreeMap

end Std
