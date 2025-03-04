/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.DTreeMap.Raw.Basic

/-
# Tree maps with unbundled well-formedness invariant

This file develops the type `Std.TreeMap.Raw` of tree maps with unbundled
well-formedness invariant.

This version is safe to use in nested inductive types. The well-formedness predicate is
available as `Std.TreeMap.Raw.WF` and we prove in this file that all operations preserve
well-formedness. When in doubt, prefer `TreeMap` over `TreeMap.Raw`.

Lemmas about the operations on `Std.TreeMap.Raw` will be available in the module
`Std.Data.TreeMap.Raw.Lemmas`.
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
module `Std.Data.TreeMap.Raw.Lemmas`.

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
  ⟨t.inner.insertIfNew a b⟩

@[inline, inherit_doc DTreeMap.Raw.containsThenInsert]
def containsThenInsert (t : Raw α β cmp) (a : α) (b : β) : Bool × Raw α β cmp :=
  let p := t.inner.containsThenInsert a b
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc DTreeMap.Raw.containsThenInsertIfNew]
def containsThenInsertIfNew (t : Raw α β cmp) (a : α) (b : β) :
    Bool × Raw α β cmp :=
  let p := t.inner.containsThenInsertIfNew a b
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc DTreeMap.Raw.getThenInsertIfNew?]
def getThenInsertIfNew? (t : Raw α β cmp) (a : α) (b : β) : Option β × Raw α β cmp :=
  let p := DTreeMap.Raw.Const.getThenInsertIfNew? t.inner a b
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

@[inline, inherit_doc DTreeMap.Raw.getKey?]
def getKey? (t : Raw α β cmp) (a : α) : Option α :=
  t.inner.getKey? a

@[inline, inherit_doc DTreeMap.Raw.getKey]
def getKey (t : Raw α β cmp) (a : α) (h : a ∈ t) : α :=
  t.inner.getKey a h

@[inline, inherit_doc DTreeMap.Raw.getKey!]
def getKey! [Inhabited α] (t : Raw α β cmp) (a : α) : α :=
  t.inner.getKey! a

@[inline, inherit_doc DTreeMap.Raw.getKeyD]
def getKeyD (t : Raw α β cmp) (a : α) (fallback : α) : α :=
  t.inner.getKeyD a fallback

@[inline, inherit_doc DTreeMap.Raw.Const.min?]
def min? (t : Raw α β cmp) : Option (α × β) :=
  DTreeMap.Raw.Const.min? t.inner

/-!
We do not provide `min` for the raw trees.
-/

@[inline, inherit_doc DTreeMap.Raw.Const.min!]
def min! [Inhabited (α × β)] (t : Raw α β cmp) : α × β :=
  DTreeMap.Raw.Const.min! t.inner

@[inline, inherit_doc DTreeMap.Raw.Const.minD]
def minD (t : Raw α β cmp) (fallback : α × β) : α × β :=
  DTreeMap.Raw.Const.minD t.inner fallback

@[inline, inherit_doc DTreeMap.Raw.Const.max?]
def max? (t : Raw α β cmp) : Option (α × β) :=
  DTreeMap.Raw.Const.max? t.inner

/-!
We do not provide `max` for the raw trees.
-/

@[inline, inherit_doc DTreeMap.Raw.Const.max!]
def max! [Inhabited (α × β)] (t : Raw α β cmp) : α × β :=
  DTreeMap.Raw.Const.max! t.inner

@[inline, inherit_doc DTreeMap.Raw.Const.maxD]
def maxD (t : Raw α β cmp) (fallback : α × β) : α × β :=
  DTreeMap.Raw.Const.maxD t.inner fallback

@[inline, inherit_doc DTreeMap.Raw.minKey?]
def minKey? (t : Raw α β cmp) : Option α :=
  DTreeMap.Raw.minKey? t.inner

/-!
We do not provide `minKey` for the raw trees.
-/

@[inline, inherit_doc DTreeMap.Raw.minKey!]
def minKey! [Inhabited α] (t : Raw α β cmp) : α :=
  DTreeMap.Raw.minKey! t.inner

@[inline, inherit_doc DTreeMap.Raw.minKeyD]
def minKeyD (t : Raw α β cmp) (fallback : α) : α :=
  DTreeMap.Raw.minKeyD t.inner fallback

@[inline, inherit_doc DTreeMap.Raw.maxKey?]
def maxKey? (t : Raw α β cmp) : Option α :=
  DTreeMap.Raw.maxKey? t.inner

/-!
We do not provide `maxKey` for the raw trees.
-/

@[inline, inherit_doc DTreeMap.Raw.maxKey!]
def maxKey! [Inhabited α] (t : Raw α β cmp) : α :=
  DTreeMap.Raw.maxKey! t.inner

@[inline, inherit_doc DTreeMap.Raw.maxKeyD]
def maxKeyD (t : Raw α β cmp) (fallback : α) : α :=
  DTreeMap.Raw.maxKeyD t.inner fallback

@[inline, inherit_doc DTreeMap.Raw.Const.entryAtIdx?]
def entryAtIdx? (t : Raw α β cmp) (n : Nat) : Option (α × β) :=
  DTreeMap.Raw.Const.entryAtIdx? t.inner n

/-!
We do not provide `entryAtIdx` for the raw trees.
-/

@[inline, inherit_doc DTreeMap.Raw.Const.entryAtIdx!]
def entryAtIdx! [Inhabited (α × β)] (t : Raw α β cmp) (n : Nat) : α × β :=
  DTreeMap.Raw.Const.entryAtIdx! t.inner n

@[inline, inherit_doc DTreeMap.Raw.Const.entryAtIdxD]
def entryAtIdxD (t : Raw α β cmp) (n : Nat) (fallback : α × β) : α × β :=
  DTreeMap.Raw.Const.entryAtIdxD t.inner n fallback

@[inline, inherit_doc DTreeMap.Raw.keyAtIndex?]
def keyAtIndex? (t : Raw α β cmp) (n : Nat) : Option α :=
  DTreeMap.Raw.keyAtIndex? t.inner n

/-!
We do not provide `keyAtIndex` for the raw trees.
-/

@[inline, inherit_doc DTreeMap.Raw.keyAtIndex!]
def keyAtIndex! [Inhabited α] (t : Raw α β cmp) (n : Nat) : α :=
  DTreeMap.Raw.keyAtIndex! t.inner n

@[inline, inherit_doc DTreeMap.Raw.keyAtIndexD]
def keyAtIndexD (t : Raw α β cmp) (n : Nat) (fallback : α) : α :=
  DTreeMap.Raw.keyAtIndexD t.inner n fallback

@[inline, inherit_doc DTreeMap.Raw.Const.getEntryGE?]
def getEntryGE? (t : Raw α β cmp) (k : α) : Option (α × β) :=
  DTreeMap.Raw.Const.getEntryGE? t.inner k

@[inline, inherit_doc DTreeMap.Raw.Const.getEntryGT?]
def getEntryGT? (t : Raw α β cmp) (k : α) : Option (α × β) :=
  DTreeMap.Raw.Const.getEntryGT? t.inner k

@[inline, inherit_doc DTreeMap.Raw.Const.getEntryLE?]
def getEntryLE? (t : Raw α β cmp) (k : α) : Option (α × β) :=
  DTreeMap.Raw.Const.getEntryLE? t.inner k

@[inline, inherit_doc DTreeMap.Raw.Const.getEntryLT?]
def getEntryLT? (t : Raw α β cmp) (k : α) : Option (α × β) :=
  DTreeMap.Raw.Const.getEntryLT? t.inner k

@[inline, inherit_doc DTreeMap.Raw.Const.getEntryGE!]
def getEntryGE! [Inhabited (α × β)] (t : Raw α β cmp) (k : α) : (α × β) :=
  DTreeMap.Raw.Const.getEntryGE! t.inner k

@[inline, inherit_doc DTreeMap.Raw.Const.getEntryGT!]
def getEntryGT! [Inhabited (α × β)] (t : Raw α β cmp) (k : α) : (α × β) :=
  DTreeMap.Raw.Const.getEntryGT! t.inner k

@[inline, inherit_doc DTreeMap.Raw.Const.getEntryLE!]
def getEntryLE! [Inhabited (α × β)] (t : Raw α β cmp) (k : α) : (α × β) :=
  DTreeMap.Raw.Const.getEntryLE! t.inner k

@[inline, inherit_doc DTreeMap.Raw.Const.getEntryLT!]
def getEntryLT! [Inhabited (α × β)] (t : Raw α β cmp) (k : α) : (α × β) :=
  DTreeMap.Raw.Const.getEntryLT! t.inner k

@[inline, inherit_doc DTreeMap.Raw.Const.getEntryGED]
def getEntryGED (t : Raw α β cmp) (k : α) (fallback : α × β) : (α × β) :=
  DTreeMap.Raw.Const.getEntryGED t.inner k fallback

@[inline, inherit_doc DTreeMap.Raw.Const.getEntryGTD]
def getEntryGTD (t : Raw α β cmp) (k : α) (fallback : α × β) : (α × β) :=
  DTreeMap.Raw.Const.getEntryGTD t.inner k fallback

@[inline, inherit_doc DTreeMap.Raw.Const.getEntryLED]
def getEntryLED (t : Raw α β cmp) (k : α) (fallback : α × β) : (α × β) :=
  DTreeMap.Raw.Const.getEntryLED t.inner k fallback

@[inline, inherit_doc DTreeMap.Raw.Const.getEntryLTD]
def getEntryLTD (t : Raw α β cmp) (k : α) (fallback : α × β) : (α × β) :=
  DTreeMap.Raw.Const.getEntryLTD t.inner k fallback

@[inline, inherit_doc DTreeMap.Raw.getKeyGE?]
def getKeyGE? (t : Raw α β cmp) (k : α) : Option α :=
  DTreeMap.Raw.getKeyGE? t.inner k

@[inline, inherit_doc DTreeMap.Raw.getKeyGT?]
def getKeyGT? (t : Raw α β cmp) (k : α) : Option α :=
  DTreeMap.Raw.getKeyGT? t.inner k

@[inline, inherit_doc DTreeMap.Raw.getKeyLE?]
def getKeyLE? (t : Raw α β cmp) (k : α) : Option α :=
  DTreeMap.Raw.getKeyLE? t.inner k

@[inline, inherit_doc DTreeMap.Raw.getKeyLT?]
def getKeyLT? (t : Raw α β cmp) (k : α) : Option α :=
  DTreeMap.Raw.getKeyLT? t.inner k

@[inline, inherit_doc DTreeMap.Raw.getKeyGE!]
def getKeyGE! [Inhabited α] (t : Raw α β cmp) (k : α) : α :=
  DTreeMap.Raw.getKeyGE! t.inner k

@[inline, inherit_doc DTreeMap.Raw.getKeyGT!]
def getKeyGT! [Inhabited α] (t : Raw α β cmp) (k : α) : α :=
  DTreeMap.Raw.getKeyGT! t.inner k

@[inline, inherit_doc DTreeMap.Raw.getKeyLE!]
def getKeyLE! [Inhabited α] (t : Raw α β cmp) (k : α) : α :=
  DTreeMap.Raw.getKeyLE! t.inner k

@[inline, inherit_doc DTreeMap.Raw.getKeyLT!]
def getKeyLT! [Inhabited α] (t : Raw α β cmp) (k : α) : α :=
  DTreeMap.Raw.getKeyLT! t.inner k

@[inline, inherit_doc DTreeMap.Raw.getKeyGED]
def getKeyGED (t : Raw α β cmp) (k : α) (fallback : α) : α :=
  DTreeMap.Raw.getKeyGED t.inner k fallback

@[inline, inherit_doc DTreeMap.Raw.getKeyGTD]
def getKeyGTD (t : Raw α β cmp) (k : α) (fallback : α) : α :=
  DTreeMap.Raw.getKeyGTD t.inner k fallback

@[inline, inherit_doc DTreeMap.Raw.getKeyLED]
def getKeyLED (t : Raw α β cmp) (k : α) (fallback : α) : α :=
  DTreeMap.Raw.getKeyLED t.inner k fallback

@[inline, inherit_doc DTreeMap.Raw.getKeyLTD]
def getKeyLTD (t : Raw α β cmp) (k : α) (fallback : α) : α :=
  DTreeMap.Raw.getKeyLTD t.inner k fallback

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

@[inline, inherit_doc DTreeMap.Raw.foldrM]
def foldrM (f : (a : α) → β → δ → m δ) (init : δ) (t : Raw α β cmp) : m δ :=
  t.inner.foldrM f init

@[inline, inherit_doc DTreeMap.Raw.foldr]
def foldr (f : (a : α) → β → δ → δ) (init : δ) (t : Raw α β cmp) : δ :=
  t.inner.foldr f init

@[inline, inherit_doc foldr, deprecated foldr (since := "2025-02-12")]
def revFold (f : δ → (a : α) → β → δ) (init : δ) (t : Raw α β cmp) : δ :=
  foldr (fun k v acc => f acc k v) init t

@[inline, inherit_doc DTreeMap.Raw.partition]
def partition (f : (a : α) → β → Bool) (t : Raw α β cmp) : Raw α β cmp × Raw α β cmp :=
  let p := t.inner.partition f; (⟨p.1⟩, ⟨p.2⟩)

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

@[inline, inherit_doc DTreeMap.Raw.values]
def values (t : Raw α β cmp) : List β :=
  t.inner.values

@[inline, inherit_doc DTreeMap.Raw.valuesArray]
def valuesArray (t : Raw α β cmp) : Array β :=
  t.inner.valuesArray

@[inline, inherit_doc DTreeMap.Raw.Const.toList]
def toList (t : Raw α β cmp) : List (α × β) :=
  DTreeMap.Raw.Const.toList t.inner

@[inline, inherit_doc DTreeMap.Raw.Const.ofList]
def ofList (l : List (α × β)) (cmp : α → α → Ordering := by exact compare) : Raw α β cmp :=
  ⟨DTreeMap.Raw.Const.ofList l cmp⟩

@[inline, inherit_doc ofList, deprecated ofList (since := "2025-02-12")]
def fromList (l : List (α × β)) (cmp : α → α → Ordering) : Raw α β cmp :=
  ofList l cmp

@[inline, inherit_doc DTreeMap.Const.unitOfList]
def unitOfList (l : List α) (cmp : α → α → Ordering := by exact compare) : Raw α Unit cmp :=
  ⟨DTreeMap.Raw.Const.unitOfList l cmp⟩

@[inline, inherit_doc DTreeMap.Raw.Const.toArray]
def toArray (t : Raw α β cmp) : Array (α × β) :=
  DTreeMap.Raw.Const.toArray t.inner

@[inline, inherit_doc DTreeMap.Raw.Const.ofArray]
def ofArray (a : Array (α × β)) (cmp : α → α → Ordering := by exact compare) : Raw α β cmp :=
  ⟨DTreeMap.Raw.Const.ofArray a cmp⟩

@[inline, inherit_doc ofArray, deprecated ofArray (since := "2025-02-12")]
def fromArray (a : Array (α × β)) (cmp : α → α → Ordering) : Raw α β cmp :=
  ofArray a cmp

@[inline, inherit_doc DTreeMap.Const.unitOfArray]
def unitOfArray (a : Array α) (cmp : α → α → Ordering := by exact compare) : Raw α Unit cmp :=
  ⟨DTreeMap.Raw.Const.unitOfArray a cmp⟩

@[inline, inherit_doc DTreeMap.Raw.Const.modify]
def modify (t : Raw α β cmp) (a : α) (f : β → β) : Raw α β cmp :=
  ⟨DTreeMap.Raw.Const.modify t.inner a f⟩

@[inline, inherit_doc DTreeMap.Raw.Const.alter]
def alter (t : Raw α β cmp) (a : α) (f : Option β → Option β) : Raw α β cmp :=
  ⟨DTreeMap.Raw.Const.alter t.inner a f⟩

@[inline, inherit_doc DTreeMap.Raw.mergeWith]
def mergeWith (mergeFn : α → β → β → β) (t₁ t₂ : Raw α β cmp) : Raw α β cmp :=
  ⟨DTreeMap.Raw.Const.mergeWith mergeFn t₁.inner t₂.inner⟩

@[inline, inherit_doc mergeWith, deprecated mergeWith (since := "2025-02-12")]
def mergeBy (mergeFn : α → β → β → β) (t₁ t₂ : Raw α β cmp) : Raw α β cmp :=
  mergeWith mergeFn t₁ t₂

@[inline, inherit_doc DTreeMap.Raw.Const.insertMany]
def insertMany {ρ} [ForIn Id ρ (α × β)] (t : Raw α β cmp) (l : ρ) : Raw α β cmp :=
  ⟨DTreeMap.Raw.Const.insertMany t.inner l⟩

@[inline, inherit_doc DTreeMap.Raw.Const.insertManyIfNewUnit]
def insertManyIfNewUnit {ρ} [ForIn Id ρ α] (t : Raw α Unit cmp) (l : ρ) : Raw α Unit cmp :=
  ⟨DTreeMap.Raw.Const.insertManyIfNewUnit t.inner l⟩

@[inline, inherit_doc DTreeMap.Raw.eraseMany]
def eraseMany {ρ} [ForIn Id ρ α] (t : Raw α β cmp) (l : ρ) : Raw α β cmp :=
  ⟨t.inner.eraseMany l⟩

instance [Repr α] [Repr β] : Repr (Raw α β cmp) where
  reprPrec m prec := Repr.addAppParen ("TreeMap.Raw.ofList " ++ repr m.toList) prec

end Raw

end TreeMap

end Std
