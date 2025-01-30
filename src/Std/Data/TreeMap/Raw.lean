/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DTreeMap.Raw

/-
# Tree maps with unbundled well-formedness invariant

This file develops the type `Std.Data.TreeMap.Raw` of tree maps with unbundled
well-formedness invariant.

This version is safe to use in nested inductive types. The well-formedness predicate is
available as `Std.Data.TreeMap.Raw.WF` and we prove in this file that all operations preserve
well-formedness. When in doubt, prefer `TreeMap` over `TreeMap.Raw`.

Lemmas about the operations on `Std.Data.TreeMap.Raw` are available in the module
`Std.Data.TreeMap.RawLemmas`.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering}

namespace Std

namespace TreeMap

/--
Tree maps without a bundled well-formedness invariant, suitable for use in nested
inductive types. The well-formedness invariant is called `Raw.WF`. When in doubt, prefer `TreeMap`
over `TreeMap.Raw`. Lemmas about the operations on `Std.Data.TreeMap.Raw` are available in the
module `Std.Data.TreeMap.RawLemmas`.

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
if any is present.

To avoid expensive copies, users should make sure that the tree map is used linearly to avoid
expensive copies.

Internally, the tree maps are represented as weight-balanced trees.
-/
structure Raw (α : Type u) (β : Type v) (cmp : α → α → Ordering) where
  /-- Internal implementation detail of the tree map. -/
  inner : DTreeMap.Raw α (fun _ => β) cmp

namespace Raw

/--
Well-formedness predicate for tree maps. Users of `TreeMap` will not need to interact with
this. Users of `TreeMap.Raw` will need to provide proofs of `WF` to lemmas and should use lemmas
like `WF.empty` and `WF.insert` (which are always named exactly like the operations they are about)
to show that map operations preserve well-formedness. The constructors of this type are internal
implementation details and should not be accessed by users.
-/
structure WF (l : Raw α β cmp) where
  /-- Internal implementation detail of the tree map. -/
  out : l.inner.WF

instance {t : Raw α β cmp} : Coe t.WF t.inner.WF where
  coe t := t.out

@[inline, inherit_doc DTreeMap.Raw.empty]
def empty : Raw α β cmp :=
  ⟨DTreeMap.Raw.empty⟩

instance : EmptyCollection (Raw α β cmp) where
  emptyCollection := empty

@[inline, inherit_doc DTreeMap.Raw.isEmpty]
def isEmpty (t : Raw α β cmp) : Bool :=
  t.inner.isEmpty

@[inline, inherit_doc DTreeMap.Raw.insert]
def insert (l : Raw α β cmp) (a : α) (b : β) : Raw α β cmp :=
  ⟨l.inner.insert a b⟩

@[inline, inherit_doc DTreeMap.Raw.insertFast]
def insertFast (l : Raw α β cmp) (h : l.WF) (a : α) (b : β) : Raw α β cmp :=
  ⟨l.inner.insertFast h.out a b⟩

@[inline, inherit_doc DTreeMap.Raw.contains]
def contains (l : Raw α β cmp) (a : α) : Bool :=
  l.inner.contains a

@[inline, inherit_doc DTreeMap.Raw.size]
def size (t : Raw α β cmp) : Nat :=
  t.inner.size

@[inline, inherit_doc DTreeMap.Raw.erase]
def erase (t : Raw α β cmp) (a : α) : Raw α β cmp :=
  ⟨t.inner.erase a⟩

@[inline, inherit_doc DTreeMap.Raw.containsThenInsert]
def containsThenInsert (t : Raw α β cmp) (a : α) (b : β) : Bool × Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsert a b
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc DTreeMap.Raw.insertIfNew]
def insertIfNew (t : Raw α β cmp) (a : α) (b : β) : Raw α β cmp :=
    letI : Ord α := ⟨cmp⟩; ⟨t.inner.insertIfNew a b⟩

@[inline, inherit_doc DTreeMap.Raw.containsThenInsertIfNew]
def containsThenInsertIfNew [BEq α] [Hashable α] (t : Raw α β cmp) (a : α) (b : β) :
    Bool × Raw α β cmp :=
  let p := t.inner.containsThenInsertIfNew a b
  (p.1, ⟨p.2⟩)

instance : Membership α (Raw α β cmp) where
  mem m a := m.contains a

instance {m : Raw α β cmp} {a : α} : Decidable (a ∈ m) :=
  show Decidable (m.contains a) from inferInstance

end Raw

end TreeMap

end Std
