/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.DTreeMap.Raw

/-
# Tree maps with unbundled well-formedness invariant

This file develops the type `Std.TreeMap.Raw` of tree maps with unbundled
well-formedness invariant.

This version is safe to use in nested inductive types. The well-formedness predicate is
available as `Std.TreeMap.Raw.WF` and we prove in this file that all operations preserve
well-formedness. When in doubt, prefer `TreeMap` over `TreeMap.Raw`.

Lemmas about the operations on `Std.TreeMap.Raw` will be available in the module
`Std.Data.TreeMap.RawLemmas`.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v w w₂

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering}

namespace Std

namespace TreeMap

/--
Tree maps without a bundled well-formedness invariant, suitable for use in nested
inductive types. The well-formedness invariant is called `Raw.WF`. When in doubt, prefer `TreeMap`
over `TreeMap.Raw`. Lemmas about the operations on `Std.TreeMap.Raw` are available in the
module `Std.Data.TreeMap.RawLemmas`.

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
-/
structure Raw (α : Type u) (β : Type v) (cmp : α → α → Ordering := by exact compare) where
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
structure WF (t : Raw α β cmp) where
  /-- Internal implementation detail of the tree map. -/
  out : t.inner.WF

instance {t : Raw α β cmp} : Coe t.WF t.inner.WF where
  coe t := t.out

@[inline, inherit_doc DTreeMap.Raw.empty]
def empty : Raw α β cmp :=
  ⟨DTreeMap.Raw.empty⟩

instance : EmptyCollection (Raw α β cmp) where
  emptyCollection := empty

instance : Inhabited (Raw α β cmp) where
  default := ∅

@[simp]
theorem empty_eq_emptyc : (empty : Raw α β cmp) = ∅ :=
  rfl

@[inline, inherit_doc DTreeMap.Raw.insert]
def insert (l : Raw α β cmp) (a : α) (b : β) : Raw α β cmp :=
  ⟨l.inner.insert a b⟩

instance : Singleton (α × β) (Raw α β cmp) where
  singleton e := (∅ : Raw α β cmp).insert e.1 e.2

instance : Insert (α × β) (Raw α β cmp) where
  insert e s := s.insert e.1 e.2

instance : LawfulSingleton (α × β) (Raw α β cmp) where
  insert_emptyc_eq _ := rfl

@[inline, inherit_doc DTreeMap.Raw.insertIfNew]
def insertIfNew (t : Raw α β cmp) (a : α) (b : β) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.insertIfNew a b⟩

@[inline, inherit_doc DTreeMap.Raw.containsThenInsert]
def containsThenInsert (t : Raw α β cmp) (a : α) (b : β) : Bool × Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsert a b
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc DTreeMap.Raw.containsThenInsertIfNew]
def containsThenInsertIfNew (t : Raw α β cmp) (a : α) (b : β) :
    Bool × Raw α β cmp :=
  let p := t.inner.containsThenInsertIfNew a b
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc DTreeMap.Raw.contains]
def contains (l : Raw α β cmp) (a : α) : Bool :=
  l.inner.contains a

instance : Membership α (Raw α β cmp) where
  mem t a := t.contains a

instance {t : Raw α β cmp} {a : α} : Decidable (a ∈ t) :=
  inferInstanceAs <| Decidable (t.contains a)

@[inline, inherit_doc DTreeMap.Raw.size]
def size (t : Raw α β cmp) : Nat :=
  t.inner.size

@[inline, inherit_doc DTreeMap.Raw.isEmpty]
def isEmpty (t : Raw α β cmp) : Bool :=
  t.inner.isEmpty

@[inline, inherit_doc DTreeMap.Raw.erase]
def erase (t : Raw α β cmp) (a : α) : Raw α β cmp :=
  ⟨t.inner.erase a⟩

@[inline, inherit_doc DTreeMap.Raw.Const.get?]
def get? (t : Raw α β cmp) (a : α) : Option β :=
  DTreeMap.Raw.Const.get? t.inner a

@[inline, inherit_doc get?, deprecated get? (since := "2025-02-12")]
def find? (t : Raw α β cmp) (a : α) : Option β :=
  get? t a

@[inline, inherit_doc DTreeMap.Raw.Const.get]
def get (t : Raw α β cmp) (a : α) (h : a ∈ t) : β :=
  DTreeMap.Raw.Const.get t.inner a h

@[inline, inherit_doc DTreeMap.Raw.Const.get!]
def get! (t : Raw α β cmp) (a : α) [Inhabited β]  : β :=
  DTreeMap.Raw.Const.get! t.inner a

@[inline, inherit_doc get!, deprecated get! (since := "2025-02-12")]
def find! (t : Raw α β cmp) (a : α) [Inhabited β] : β :=
  get! t a

@[inline, inherit_doc DTreeMap.Raw.Const.getD]
def getD (t : Raw α β cmp) (a : α) (fallback : β) : β :=
  DTreeMap.Raw.Const.getD t.inner a fallback

@[inline, inherit_doc getD, deprecated getD (since := "2025-02-12")]
def findD (t : Raw α β cmp) (a : α) (fallback : β) : β :=
  getD t a fallback

instance : GetElem? (Raw α β cmp) α β (fun m a => a ∈ m) where
  getElem m a h := m.get a h
  getElem? m a := m.get? a
  getElem! m a := m.get! a

variable {δ : Type w} {m : Type w → Type w₂} [Monad m]

@[inline, inherit_doc DTreeMap.Raw.filter]
def filter (f : α → β → Bool) (t : Raw α β cmp) : Raw α β cmp :=
  ⟨t.inner.filter f⟩

@[inline, inherit_doc DTreeMap.Raw.foldlM]
def foldlM (f : δ → (a : α) → β → m δ) (init : δ) (t : Raw α β cmp) : m δ :=
  t.inner.foldlM f init

@[inline, inherit_doc foldlM, deprecated foldlM (since := "2025-02-12")]
def foldM (f : δ → (a : α) → β → m δ) (init : δ) (t : Raw α β cmp) : m δ :=
  t.foldlM f init

@[inline, inherit_doc DTreeMap.Raw.foldl]
def foldl (f : δ → (a : α) → β → δ) (init : δ) (t : Raw α β cmp) : δ :=
  t.inner.foldl f init

@[inline, inherit_doc foldl, deprecated foldl (since := "2025-02-12")]
def fold (f : δ → (a : α) → β → δ) (init : δ) (t : Raw α β cmp) : δ :=
  t.foldl f init

@[inline, inherit_doc DTreeMap.Raw.forM]
def forM (f : α → β → m PUnit) (t : Raw α β cmp) : m PUnit :=
  t.inner.forM f

@[inline, inherit_doc DTreeMap.Raw.forIn]
def forIn (f : α → β → δ → m (ForInStep δ)) (init : δ) (t : Raw α β cmp) : m δ :=
  t.inner.forIn (fun a b c => f a b c) init

instance : ForM m (Raw α β cmp) (α × β) where
  forM t f := t.forM (fun a b => f ⟨a, b⟩)

instance : ForIn m (Raw α β cmp) (α × β) where
  forIn t init f := t.forIn (fun a b acc => f ⟨a, b⟩ acc) init

@[inline, inherit_doc DTreeMap.Raw.any]
def any (t : Raw α β cmp) (p : α → β → Bool) : Bool :=
  t.inner.any p

@[inline, inherit_doc DTreeMap.Raw.all]
def all (t : Raw α β cmp) (p : α → β → Bool) : Bool :=
  t.inner.all p

@[inline, inherit_doc DTreeMap.Raw.keys]
def keys (t : Raw α β cmp) : List α :=
  t.inner.keys

@[inline, inherit_doc DTreeMap.Raw.keysArray]
def keysArray (t : Raw α β cmp) : Array α :=
  t.inner.keysArray

@[inline, inherit_doc DTreeMap.Raw.toList]
def toList (t : Raw α β cmp) : List (α × β) :=
  DTreeMap.Raw.Const.toList t.inner

@[inline, inherit_doc DTreeMap.Raw.toArray]
def toArray (t : Raw α β cmp) : Array (α × β) :=
  DTreeMap.Raw.Const.toArray t.inner

@[inline, inherit_doc DTreeMap.Raw.mergeWith]
def mergeWith (mergeFn : α → β → β → β) (t₁ t₂ : Raw α β cmp) : Raw α β cmp :=
  ⟨DTreeMap.Raw.Const.mergeWith mergeFn t₁.inner t₂.inner⟩

@[inline, inherit_doc mergeWith, deprecated mergeWith (since := "2025-02-12")]
def mergeBy (mergeFn : α → β → β → β) (t₁ t₂ : Raw α β cmp) : Raw α β cmp :=
  mergeWith mergeFn t₁ t₂

@[inline, inherit_doc DTreeMap.Raw.eraseMany]
def eraseMany {ρ} [ForIn Id ρ α] (t : Raw α β cmp) (l : ρ) : Raw α β cmp :=
  ⟨t.inner.eraseMany l⟩

instance [Repr α] [Repr β] : Repr (Raw α β cmp) where
  reprPrec m prec := Repr.addAppParen ("TreeMap.Raw.ofList " ++ repr m.toList) prec

end Raw

end TreeMap

end Std
