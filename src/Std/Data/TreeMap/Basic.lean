/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.DTreeMap.Basic

/-!
# Tree maps

This file develops the type `Std.TreeMap` of tree maps.

Lemmas about the operations on `Std.TreeMap` will be available in the
module `Std.Data.TreeMap.Lemmas`.

See the module `Std.Data.TreeMap.Raw` for a variant of this type which is safe to use in
nested inductive types.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v w w₂

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering}

namespace Std

/--
Tree maps.

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
if any is present.

To avoid expensive copies, users should make sure that the tree map is used linearly.

Internally, the tree maps are represented as size-bounded trees, a type of self-balancing binary
search tree with efficient order statistic lookups.

These tree maps contain a bundled well-formedness invariant, which means that they cannot
be used in nested inductive types. For these use cases, `Std.Data.TreeMap.Raw` and
`Std.Data.TreeMap.Raw.WF` unbundle the invariant from the tree map. When in doubt, prefer
`TreeMap` over `TreeMap.Raw`.
-/
structure TreeMap (α : Type u) (β : Type v) (cmp : α → α → Ordering := by exact compare) where
  /-- Internal implementation detail of the tree map. -/
  inner : DTreeMap α (fun _ => β) cmp

namespace TreeMap

@[inline, inherit_doc DTreeMap.empty]
def empty : TreeMap α β cmp :=
  ⟨DTreeMap.empty⟩

instance : EmptyCollection (TreeMap α β cmp) where
  emptyCollection := empty

instance : Inhabited (TreeMap α β cmp) := ⟨∅⟩

@[simp]
theorem empty_eq_emptyc : (empty : TreeMap α β cmp) = ∅ :=
  rfl

@[inline, inherit_doc DTreeMap.insert]
def insert (l : TreeMap α β cmp) (a : α) (b : β) : TreeMap α β cmp :=
  ⟨l.inner.insert a b⟩

instance : Singleton (α × β) (TreeMap α β cmp) where
  singleton e := (∅ : TreeMap α β cmp).insert e.1 e.2

instance : Insert (α × β) (TreeMap α β cmp) where
  insert e s := s.insert e.1 e.2

instance : LawfulSingleton (α × β) (TreeMap α β cmp) where
  insert_emptyc_eq _ := rfl

@[inline, inherit_doc DTreeMap.insertIfNew]
def insertIfNew (t : TreeMap α β cmp) (a : α) (b : β) : TreeMap α β cmp :=
  ⟨t.inner.insertIfNew a b⟩

@[inline, inherit_doc DTreeMap.containsThenInsert]
def containsThenInsert (t : TreeMap α β cmp) (a : α) (b : β) : Bool × TreeMap α β cmp :=
  let p := t.inner.containsThenInsert a b
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc DTreeMap.containsThenInsertIfNew]
def containsThenInsertIfNew (t : TreeMap α β cmp) (a : α) (b : β) :
    Bool × TreeMap α β cmp :=
  let p := t.inner.containsThenInsertIfNew a b
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc DTreeMap.contains]
def contains (l : TreeMap α β cmp) (a : α) : Bool :=
  l.inner.contains a

instance : Membership α (TreeMap α β cmp) where
  mem m a := m.contains a

instance {m : TreeMap α β cmp} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs <| Decidable (m.contains a)

@[inline, inherit_doc DTreeMap.size]
def size (t : TreeMap α β cmp) : Nat :=
  t.inner.size

@[inline, inherit_doc DTreeMap.isEmpty]
def isEmpty (t : TreeMap α β cmp) : Bool :=
  t.inner.isEmpty

@[inline, inherit_doc DTreeMap.erase]
def erase (t : TreeMap α β cmp) (a : α) : TreeMap α β cmp :=
  ⟨t.inner.erase a⟩

@[inline, inherit_doc DTreeMap.get?]
def get? (t : TreeMap α β cmp) (a : α) : Option β :=
  DTreeMap.Const.get? t.inner a

@[inline, inherit_doc DTreeMap.get]
def get (t : TreeMap α β cmp) (a : α) (h : a ∈ t) : β :=
   DTreeMap.Const.get t.inner a h

@[inline, inherit_doc DTreeMap.get!]
def get! (t : TreeMap α β cmp) (a : α) [Inhabited β]  : β :=
  DTreeMap.Const.get! t.inner a

@[inline, inherit_doc DTreeMap.getD]
def getD (t : TreeMap α β cmp) (a : α) (fallback : β) : β :=
  DTreeMap.Const.getD t.inner a fallback

instance : GetElem? (TreeMap α β cmp) α β (fun m a => a ∈ m) where
  getElem m a h := m.get a h
  getElem? m a := m.get? a
  getElem! m a := m.get! a

variable {δ : Type w} {m : Type w → Type w₂} [Monad m]

@[inline, inherit_doc DTreeMap.filter]
def filter (f : α → β → Bool) (m : TreeMap α β cmp) : TreeMap α β cmp :=
  ⟨m.inner.filter f⟩

@[inline, inherit_doc DTreeMap.foldlM]
def foldlM (f : δ → (a : α) → β → m δ) (init : δ) (t : TreeMap α β cmp) : m δ :=
  t.inner.foldlM f init

@[inline, inherit_doc DTreeMap.foldl]
def foldl (f : δ → (a : α) → β → δ) (init : δ) (t : TreeMap α β cmp) : δ :=
  t.inner.foldl f init

@[inline, inherit_doc DTreeMap.forM]
def forM (f : α → β → m PUnit) (t : TreeMap α β cmp) : m PUnit :=
  t.inner.forM f

@[inline, inherit_doc DTreeMap.forIn]
def forIn (f : α → β → δ → m (ForInStep δ)) (init : δ) (t : TreeMap α β cmp) : m δ :=
  t.inner.forIn (fun a b c => f a b c) init

instance : ForM m (TreeMap α β cmp) (α × β) where
  forM t f := t.forM (fun a b => f ⟨a, b⟩)

instance : ForIn m (TreeMap α β cmp) (α × β) where
  forIn m init f := m.forIn (fun a b acc => f ⟨a, b⟩ acc) init

@[inline, inherit_doc DTreeMap.any]
def any (t : TreeMap α β cmp) (p : α → β → Bool) : Bool :=
  t.inner.any p

@[inline, inherit_doc DTreeMap.all]
def all (t : TreeMap α β cmp) (p : α → β → Bool) : Bool :=
  t.inner.all p

@[inline, inherit_doc DTreeMap.keys]
def keys (t : TreeMap α β cmp) : List α :=
  t.inner.keys

@[inline, inherit_doc DTreeMap.keysArray]
def keysArray (t : TreeMap α β cmp) : Array α :=
  t.inner.keysArray

@[inline, inherit_doc DTreeMap.Const.toList]
def toList (t : TreeMap α β cmp) : List (α × β) :=
  DTreeMap.Const.toList t.inner

@[inline, inherit_doc DTreeMap.Const.toArray]
def toArray (t : TreeMap α β cmp) : Array (α × β) :=
  DTreeMap.Const.toArray t.inner

@[inline, inherit_doc DTreeMap.mergeWith]
def mergeWith (mergeFn : α → β → β → β) (t₁ t₂ : TreeMap α β cmp) : TreeMap α β cmp :=
  ⟨DTreeMap.Const.mergeWith mergeFn t₁.inner t₂.inner⟩

@[inline, inherit_doc DTreeMap.eraseMany]
def eraseMany {ρ} [ForIn Id ρ α] (t : TreeMap α β cmp) (l : ρ) : TreeMap α β cmp :=
  ⟨t.inner.eraseMany l⟩

instance [Repr α] [Repr β] : Repr (TreeMap α β cmp) where
  reprPrec m prec := Repr.addAppParen ("TreeMap.ofList " ++ repr m.toList) prec

end TreeMap

end Std
