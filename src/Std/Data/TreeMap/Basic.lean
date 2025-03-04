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

See the module `Std.Data.TreeMap.Raw.Basic` for a variant of this type which is safe to use in
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
be used in nested inductive types. For these use cases, `Std.TreeMap.Raw` and
`Std.TreeMap.Raw.WF` unbundle the invariant from the tree map. When in doubt, prefer
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

@[inline, inherit_doc DTreeMap.getThenInsertIfNew?]
def getThenInsertIfNew? (t : TreeMap α β cmp) (a : α) (b : β) : Option β × TreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := DTreeMap.Const.getThenInsertIfNew? t.inner a b
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

@[inline, inherit_doc DTreeMap.Const.get?]
def get? (t : TreeMap α β cmp) (a : α) : Option β :=
  DTreeMap.Const.get? t.inner a

@[inline, inherit_doc get?, deprecated get? (since := "2025-02-12")]
def find? (t : TreeMap α β cmp) (a : α) : Option β :=
  get? t a

@[inline, inherit_doc DTreeMap.Const.get]
def get (t : TreeMap α β cmp) (a : α) (h : a ∈ t) : β :=
  DTreeMap.Const.get t.inner a h

@[inline, inherit_doc DTreeMap.Const.get!]
def get! (t : TreeMap α β cmp) (a : α) [Inhabited β] : β :=
  DTreeMap.Const.get! t.inner a

@[inline, inherit_doc get!, deprecated get! (since := "2025-02-12")]
def find! (t : TreeMap α β cmp) (a : α) [Inhabited β] : β :=
  get! t a

@[inline, inherit_doc DTreeMap.Const.getD]
def getD (t : TreeMap α β cmp) (a : α) (fallback : β) : β :=
  DTreeMap.Const.getD t.inner a fallback

@[inline, inherit_doc getD, deprecated getD (since := "2025-02-12")]
def findD (t : TreeMap α β cmp) (a : α) (fallback : β) : β :=
  getD t a fallback

instance : GetElem? (TreeMap α β cmp) α β (fun m a => a ∈ m) where
  getElem m a h := m.get a h
  getElem? m a := m.get? a
  getElem! m a := m.get! a

@[inline, inherit_doc DTreeMap.getKey?]
def getKey? (t : TreeMap α β cmp) (a : α) : Option α :=
  t.inner.getKey? a

@[inline, inherit_doc DTreeMap.getKey]
def getKey (t : TreeMap α β cmp) (a : α) (h : a ∈ t) : α :=
  t.inner.getKey a h

@[inline, inherit_doc DTreeMap.getKey!]
def getKey! [Inhabited α] (t : TreeMap α β cmp) (a : α) : α :=
  t.inner.getKey! a

@[inline, inherit_doc DTreeMap.getKeyD]
def getKeyD (t : TreeMap α β cmp) (a : α) (fallback : α) : α :=
  t.inner.getKeyD a fallback

@[inline, inherit_doc DTreeMap.Const.min?]
def min? (t : TreeMap α β cmp) : Option (α × β) :=
  DTreeMap.Const.min? t.inner

@[inline, inherit_doc DTreeMap.Const.min]
def min (t : TreeMap α β cmp) (h : t.isEmpty = false) : α × β :=
  DTreeMap.Const.min t.inner h

@[inline, inherit_doc DTreeMap.Const.min!]
def min! [Inhabited (α × β)] (t : TreeMap α β cmp) : α × β :=
  DTreeMap.Const.min! t.inner

@[inline, inherit_doc DTreeMap.Const.minD]
def minD (t : TreeMap α β cmp) (fallback : α × β) : α × β :=
  DTreeMap.Const.minD t.inner fallback

@[inline, inherit_doc DTreeMap.Const.max?]
def max? (t : TreeMap α β cmp) : Option (α × β) :=
  DTreeMap.Const.max? t.inner

@[inline, inherit_doc DTreeMap.Const.max]
def max (t : TreeMap α β cmp) (h : t.isEmpty = false) : α × β :=
  DTreeMap.Const.max t.inner h

@[inline, inherit_doc DTreeMap.Const.max!]
def max! [Inhabited (α × β)] (t : TreeMap α β cmp) : α × β :=
  DTreeMap.Const.max! t.inner

@[inline, inherit_doc DTreeMap.Const.maxD]
def maxD (t : TreeMap α β cmp) (fallback : α × β) : α × β :=
  DTreeMap.Const.maxD t.inner fallback

@[inline, inherit_doc DTreeMap.minKey?]
def minKey? (t : TreeMap α β cmp) : Option α :=
  DTreeMap.minKey? t.inner

@[inline, inherit_doc DTreeMap.minKey]
def minKey (t : TreeMap α β cmp) (h : t.isEmpty = false) : α :=
  DTreeMap.minKey t.inner h

@[inline, inherit_doc DTreeMap.minKey!]
def minKey! [Inhabited α] (t : TreeMap α β cmp) : α :=
  DTreeMap.minKey! t.inner

@[inline, inherit_doc DTreeMap.minKeyD]
def minKeyD (t : TreeMap α β cmp) (fallback : α) : α :=
  DTreeMap.minKeyD t.inner fallback

@[inline, inherit_doc DTreeMap.maxKey?]
def maxKey? (t : TreeMap α β cmp) : Option α :=
  DTreeMap.maxKey? t.inner

@[inline, inherit_doc DTreeMap.maxKey]
def maxKey (t : TreeMap α β cmp) (h : t.isEmpty = false) : α :=
  DTreeMap.maxKey t.inner h

@[inline, inherit_doc DTreeMap.maxKey!]
def maxKey! [Inhabited α] (t : TreeMap α β cmp) : α :=
  DTreeMap.maxKey! t.inner

@[inline, inherit_doc DTreeMap.maxKeyD]
def maxKeyD (t : TreeMap α β cmp) (fallback : α) : α :=
  DTreeMap.maxKeyD t.inner fallback

@[inline, inherit_doc DTreeMap.Const.entryAtIdx?]
def entryAtIdx? (t : TreeMap α β cmp) (n : Nat) : Option (α × β) :=
  DTreeMap.Const.entryAtIdx? t.inner n

@[inline, inherit_doc DTreeMap.Const.entryAtIdx]
def entryAtIdx (t : TreeMap α β cmp) (n : Nat) (h : n < t.size) : α × β :=
  DTreeMap.Const.entryAtIdx t.inner n h

@[inline, inherit_doc DTreeMap.Const.entryAtIdx!]
def entryAtIdx! [Inhabited (α × β)] (t : TreeMap α β cmp) (n : Nat) : α × β :=
  DTreeMap.Const.entryAtIdx! t.inner n

@[inline, inherit_doc DTreeMap.Const.entryAtIdxD]
def entryAtIdxD (t : TreeMap α β cmp) (n : Nat) (fallback : α × β) : α × β :=
  DTreeMap.Const.entryAtIdxD t.inner n fallback

@[inline, inherit_doc DTreeMap.keyAtIndex?]
def keyAtIndex? (t : TreeMap α β cmp) (n : Nat) : Option α :=
  DTreeMap.keyAtIndex? t.inner n

@[inline, inherit_doc DTreeMap.keyAtIndex]
def keyAtIndex (t : TreeMap α β cmp) (n : Nat) (h : n < t.size) : α :=
  DTreeMap.keyAtIndex t.inner n h

@[inline, inherit_doc DTreeMap.keyAtIndex!]
def keyAtIndex! [Inhabited α] (t : TreeMap α β cmp) (n : Nat) : α :=
  DTreeMap.keyAtIndex! t.inner n

@[inline, inherit_doc DTreeMap.keyAtIndexD]
def keyAtIndexD (t : TreeMap α β cmp) (n : Nat) (fallback : α) : α :=
  DTreeMap.keyAtIndexD t.inner n fallback

@[inline, inherit_doc DTreeMap.Const.getEntryGE?]
def getEntryGE? (t : TreeMap α β cmp) (k : α) : Option (α × β) :=
  DTreeMap.Const.getEntryGE? t.inner k

@[inline, inherit_doc DTreeMap.Const.getEntryGT?]
def getEntryGT? (t : TreeMap α β cmp) (k : α) : Option (α × β) :=
  DTreeMap.Const.getEntryGT? t.inner k

@[inline, inherit_doc DTreeMap.Const.getEntryLE?]
def getEntryLE? (t : TreeMap α β cmp) (k : α) : Option (α × β) :=
  DTreeMap.Const.getEntryLE? t.inner k

@[inline, inherit_doc DTreeMap.Const.getEntryLT?]
def getEntryLT? (t : TreeMap α β cmp) (k : α) : Option (α × β) :=
  DTreeMap.Const.getEntryLT? t.inner k

/-!
`getEntryGE`, `getEntryGT`, `getEntryLE`, `getEntryLT` can be found in
`Std.Data.TreeMap.AdditionalOperations`.
-/

@[inline, inherit_doc DTreeMap.Const.getEntryGE!]
def getEntryGE! [Inhabited (α × β)] (t : TreeMap α β cmp) (k : α) : (α × β) :=
  DTreeMap.Const.getEntryGE! t.inner k

@[inline, inherit_doc DTreeMap.Const.getEntryGT!]
def getEntryGT! [Inhabited (α × β)] (t : TreeMap α β cmp) (k : α) : (α × β) :=
  DTreeMap.Const.getEntryGT! t.inner k

@[inline, inherit_doc DTreeMap.Const.getEntryLE!]
def getEntryLE! [Inhabited (α × β)] (t : TreeMap α β cmp) (k : α) : (α × β) :=
  DTreeMap.Const.getEntryLE! t.inner k

@[inline, inherit_doc DTreeMap.Const.getEntryLT!]
def getEntryLT! [Inhabited (α × β)] (t : TreeMap α β cmp) (k : α) : (α × β) :=
  DTreeMap.Const.getEntryLT! t.inner k

@[inline, inherit_doc DTreeMap.Const.getEntryGED]
def getEntryGED (t : TreeMap α β cmp) (k : α) (fallback : α × β) : (α × β) :=
  DTreeMap.Const.getEntryGED t.inner k fallback

@[inline, inherit_doc DTreeMap.Const.getEntryGTD]
def getEntryGTD (t : TreeMap α β cmp) (k : α) (fallback : α × β) : (α × β) :=
  DTreeMap.Const.getEntryGTD t.inner k fallback

@[inline, inherit_doc DTreeMap.Const.getEntryLED]
def getEntryLED (t : TreeMap α β cmp) (k : α) (fallback : α × β) : (α × β) :=
  DTreeMap.Const.getEntryLED t.inner k fallback

@[inline, inherit_doc DTreeMap.Const.getEntryLTD]
def getEntryLTD (t : TreeMap α β cmp) (k : α) (fallback : α × β) : (α × β) :=
  DTreeMap.Const.getEntryLTD t.inner k fallback

@[inline, inherit_doc DTreeMap.getKeyGE?]
def getKeyGE? (t : TreeMap α β cmp) (k : α) : Option α :=
  DTreeMap.getKeyGE? t.inner k

@[inline, inherit_doc DTreeMap.getKeyGT?]
def getKeyGT? (t : TreeMap α β cmp) (k : α) : Option α :=
  DTreeMap.getKeyGT? t.inner k

@[inline, inherit_doc DTreeMap.getKeyLE?]
def getKeyLE? (t : TreeMap α β cmp) (k : α) : Option α :=
  DTreeMap.getKeyLE? t.inner k

@[inline, inherit_doc DTreeMap.getKeyLT?]
def getKeyLT? (t : TreeMap α β cmp) (k : α) : Option α :=
  DTreeMap.getKeyLT? t.inner k

/-!
`getKeyGE`, `getKeyGT`, `getKeyLE`, `getKeyLT` can be found in
`Std.Data.TreeMap.AdditionalOperations`.
-/

@[inline, inherit_doc DTreeMap.getKeyGE!]
def getKeyGE! [Inhabited α] (t : TreeMap α β cmp) (k : α) : α :=
  DTreeMap.getKeyGE! t.inner k

@[inline, inherit_doc DTreeMap.getKeyGT!]
def getKeyGT! [Inhabited α] (t : TreeMap α β cmp) (k : α) : α :=
  DTreeMap.getKeyGT! t.inner k

@[inline, inherit_doc DTreeMap.getKeyLE!]
def getKeyLE! [Inhabited α] (t : TreeMap α β cmp) (k : α) : α :=
  DTreeMap.getKeyLE! t.inner k

@[inline, inherit_doc DTreeMap.getKeyLT!]
def getKeyLT! [Inhabited α] (t : TreeMap α β cmp) (k : α) : α :=
  DTreeMap.getKeyLT! t.inner k

@[inline, inherit_doc DTreeMap.getKeyGED]
def getKeyGED (t : TreeMap α β cmp) (k : α) (fallback : α) : α :=
  DTreeMap.getKeyGED t.inner k fallback

@[inline, inherit_doc DTreeMap.getKeyGTD]
def getKeyGTD (t : TreeMap α β cmp) (k : α) (fallback : α) : α :=
  DTreeMap.getKeyGTD t.inner k fallback

@[inline, inherit_doc DTreeMap.getKeyLED]
def getKeyLED (t : TreeMap α β cmp) (k : α) (fallback : α) : α :=
  DTreeMap.getKeyLED t.inner k fallback

@[inline, inherit_doc DTreeMap.getKeyLTD]
def getKeyLTD (t : TreeMap α β cmp) (k : α) (fallback : α) : α :=
  DTreeMap.getKeyLTD t.inner k fallback

variable {δ : Type w} {m : Type w → Type w₂} [Monad m]

@[inline, inherit_doc DTreeMap.filter]
def filter (f : α → β → Bool) (m : TreeMap α β cmp) : TreeMap α β cmp :=
  ⟨m.inner.filter f⟩

@[inline, inherit_doc DTreeMap.foldlM]
def foldlM (f : δ → (a : α) → β → m δ) (init : δ) (t : TreeMap α β cmp) : m δ :=
  t.inner.foldlM f init

@[inline, inherit_doc foldlM, deprecated foldlM (since := "2025-02-12")]
def foldM (f : δ → (a : α) → β → m δ) (init : δ) (t : TreeMap α β cmp) : m δ :=
  t.foldlM f init

@[inline, inherit_doc DTreeMap.foldl]
def foldl (f : δ → (a : α) → β → δ) (init : δ) (t : TreeMap α β cmp) : δ :=
  t.inner.foldl f init

@[inline, inherit_doc foldl, deprecated foldl (since := "2025-02-12")]
def fold (f : δ → (a : α) → β → δ) (init : δ) (t : TreeMap α β cmp) : δ :=
  t.foldl f init

@[inline, inherit_doc DTreeMap.foldrM]
def foldrM (f : (a : α) → β → δ → m δ) (init : δ) (t : TreeMap α β cmp) : m δ :=
  t.inner.foldrM f init

@[inline, inherit_doc DTreeMap.foldr]
def foldr (f : (a : α) → β → δ → δ) (init : δ) (t : TreeMap α β cmp) : δ :=
  t.inner.foldr f init

@[inline, inherit_doc foldr, deprecated foldr (since := "2025-02-12")]
def revFold (f : δ → (a : α) → β → δ) (init : δ) (t : TreeMap α β cmp) : δ :=
  foldr (fun k v acc => f acc k v) init t

@[inline, inherit_doc DTreeMap.partition]
def partition (f : (a : α) → β → Bool) (t : TreeMap α β cmp) : TreeMap α β cmp × TreeMap α β cmp :=
  let p := t.inner.partition f; (⟨p.1⟩, ⟨p.2⟩)

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

@[inline, inherit_doc DTreeMap.values]
def values (t : TreeMap α β cmp) : List β :=
  t.inner.values

@[inline, inherit_doc DTreeMap.valuesArray]
def valuesArray (t : TreeMap α β cmp) : Array β :=
  t.inner.valuesArray

@[inline, inherit_doc DTreeMap.Const.toList]
def toList (t : TreeMap α β cmp) : List (α × β) :=
  DTreeMap.Const.toList t.inner

@[inline, inherit_doc DTreeMap.Const.ofList]
def ofList (l : List (α × β)) (cmp : α → α → Ordering := by exact compare) : TreeMap α β cmp :=
  ⟨DTreeMap.Const.ofList l cmp⟩

@[inline, inherit_doc ofList, deprecated ofList (since := "2025-02-12")]
def fromList (l : List (α × β)) (cmp : α → α → Ordering) : TreeMap α β cmp :=
  ofList l cmp

@[inline, inherit_doc DTreeMap.Const.unitOfList]
def unitOfList (l : List α) (cmp : α → α → Ordering := by exact compare) : TreeMap α Unit cmp :=
  ⟨DTreeMap.Const.unitOfList l cmp⟩

@[inline, inherit_doc DTreeMap.Const.toArray]
def toArray (t : TreeMap α β cmp) : Array (α × β) :=
  DTreeMap.Const.toArray t.inner

@[inline, inherit_doc DTreeMap.Const.ofArray]
def ofArray (a : Array (α × β)) (cmp : α → α → Ordering := by exact compare) : TreeMap α β cmp :=
  ⟨DTreeMap.Const.ofArray a cmp⟩

@[inline, inherit_doc ofArray, deprecated ofArray (since := "2025-02-12")]
def fromArray (a : Array (α × β)) (cmp : α → α → Ordering) : TreeMap α β cmp :=
  ofArray a cmp

@[inline, inherit_doc DTreeMap.Const.unitOfArray]
def unitOfArray (a : Array α) (cmp : α → α → Ordering := by exact compare) : TreeMap α Unit cmp :=
  ⟨DTreeMap.Const.unitOfArray a cmp⟩

@[inline, inherit_doc DTreeMap.Const.modify]
def modify (t : TreeMap α β cmp) (a : α) (f : β → β) : TreeMap α β cmp :=
  ⟨DTreeMap.Const.modify t.inner a f⟩

@[inline, inherit_doc DTreeMap.Const.alter]
def alter (t : TreeMap α β cmp) (a : α) (f : Option β → Option β) : TreeMap α β cmp :=
  ⟨DTreeMap.Const.alter t.inner a f⟩

@[inline, inherit_doc DTreeMap.Const.mergeWith]
def mergeWith (mergeFn : α → β → β → β) (t₁ t₂ : TreeMap α β cmp) : TreeMap α β cmp :=
  ⟨DTreeMap.Const.mergeWith mergeFn t₁.inner t₂.inner⟩

@[inline, inherit_doc mergeWith, deprecated mergeWith (since := "2025-02-12")]
def mergeBy (mergeFn : α → β → β → β) (t₁ t₂ : TreeMap α β cmp) : TreeMap α β cmp :=
  mergeWith mergeFn t₁ t₂

@[inline, inherit_doc DTreeMap.Const.insertMany]
def insertMany {ρ} [ForIn Id ρ (α × β)] (t : TreeMap α β cmp) (l : ρ) : TreeMap α β cmp :=
  ⟨DTreeMap.Const.insertMany t.inner l⟩

@[inline, inherit_doc DTreeMap.Const.insertManyIfNewUnit]
def insertManyIfNewUnit {ρ} [ForIn Id ρ α] (t : TreeMap α Unit cmp) (l : ρ) : TreeMap α Unit cmp :=
  ⟨DTreeMap.Const.insertManyIfNewUnit t.inner l⟩

@[inline, inherit_doc DTreeMap.eraseMany]
def eraseMany {ρ} [ForIn Id ρ α] (t : TreeMap α β cmp) (l : ρ) : TreeMap α β cmp :=
  ⟨t.inner.eraseMany l⟩

instance [Repr α] [Repr β] : Repr (TreeMap α β cmp) where
  reprPrec m prec := Repr.addAppParen ("TreeMap.ofList " ++ repr m.toList) prec

end TreeMap

end Std
