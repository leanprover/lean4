/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez, Markus Himmel, Paul Reichert
-/
module

prelude
public import Std.Data.ExtDTreeMap.Basic

@[expose] public section

/-!
# Extensional tree maps

This file develops the type `Std.ExtTreeMap` of tree maps.

Lemmas about the operations on `Std.ExtTreeMap` will be available in the
module `Std.Data.ExtTreeMap.Lemmas`.

See the module `Std.Data.TreeMap.Raw.Basic` for a variant of this type which is safe to use in
nested inductive types.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v w w₂

variable {α : Type u} {β : Type v} {γ : Type w} {cmp : α → α → Ordering}

namespace Std

/--
Extensional tree maps.

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

In contrast to regular tree maps, `Std.ExtTreeMap` offers several extensionality lemmas
and therefore has more lemmas about equality of tree maps. This doesn't affect the amount of
supported functions though: `Std.ExtTreeMap` supports all operations from `Std.TreeMap`.

In order to use most functions, a `TransCmp` instance is required. This is necessary to make sure
that the functions are congruent, i.e. equivalent tree maps as parameters produce equivalent return
values.

These tree maps contain a bundled well-formedness invariant, which means that they cannot
be used in nested inductive types. For these use cases, `Std.TreeMap.Raw` and
`Std.TreeMap.Raw.WF` unbundle the invariant from the tree map. When in doubt, prefer
`ExtTreeMap` over `TreeMap.Raw`.
-/
structure ExtTreeMap (α : Type u) (β : Type v) (cmp : α → α → Ordering := by exact compare) where
  /-- Internal implementation detail of the tree map. -/
  inner : ExtDTreeMap α (fun _ => β) cmp

namespace ExtTreeMap

@[inline, inherit_doc ExtDTreeMap.empty]
def empty : ExtTreeMap α β cmp :=
  ⟨ExtDTreeMap.empty⟩

instance : EmptyCollection (ExtTreeMap α β cmp) where
  emptyCollection := empty

instance : Inhabited (ExtTreeMap α β cmp) := ⟨∅⟩

@[simp, grind =]
theorem empty_eq_emptyc : (empty : ExtTreeMap α β cmp) = ∅ :=
  rfl

@[inline, inherit_doc ExtDTreeMap.insert]
def insert [TransCmp cmp] (l : ExtTreeMap α β cmp) (a : α) (b : β) : ExtTreeMap α β cmp :=
  ⟨l.inner.insert a b⟩

instance [TransCmp cmp] : Singleton (α × β) (ExtTreeMap α β cmp) where
  singleton e := (∅ : ExtTreeMap α β cmp).insert e.1 e.2

instance [TransCmp cmp] : Insert (α × β) (ExtTreeMap α β cmp) where
  insert e s := s.insert e.1 e.2

instance [TransCmp cmp] : LawfulSingleton (α × β) (ExtTreeMap α β cmp) where
  insert_empty_eq _ := rfl

@[inline, inherit_doc ExtDTreeMap.insertIfNew]
def insertIfNew [TransCmp cmp] (t : ExtTreeMap α β cmp) (a : α) (b : β) : ExtTreeMap α β cmp :=
  ⟨t.inner.insertIfNew a b⟩

@[inline, inherit_doc ExtDTreeMap.containsThenInsert]
def containsThenInsert [TransCmp cmp] (t : ExtTreeMap α β cmp) (a : α) (b : β) : Bool × ExtTreeMap α β cmp :=
  let p := t.inner.containsThenInsert a b
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc ExtDTreeMap.containsThenInsertIfNew]
def containsThenInsertIfNew [TransCmp cmp] (t : ExtTreeMap α β cmp) (a : α) (b : β) :
    Bool × ExtTreeMap α β cmp :=
  let p := t.inner.containsThenInsertIfNew a b
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc ExtDTreeMap.getThenInsertIfNew?]
def getThenInsertIfNew? [TransCmp cmp] (t : ExtTreeMap α β cmp) (a : α) (b : β) : Option β × ExtTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := ExtDTreeMap.Const.getThenInsertIfNew? t.inner a b
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc ExtDTreeMap.contains]
def contains [TransCmp cmp] (l : ExtTreeMap α β cmp) (a : α) : Bool :=
  l.inner.contains a

instance [TransCmp cmp] : Membership α (ExtTreeMap α β cmp) where
  mem m a := m.contains a

instance [TransCmp cmp] {m : ExtTreeMap α β cmp} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs <| Decidable (m.contains a)

@[inline, inherit_doc ExtDTreeMap.size]
def size (t : ExtTreeMap α β cmp) : Nat :=
  t.inner.size

@[inline, inherit_doc ExtDTreeMap.isEmpty]
def isEmpty (t : ExtTreeMap α β cmp) : Bool :=
  t.inner.isEmpty

@[inline, inherit_doc ExtDTreeMap.erase]
def erase [TransCmp cmp] (t : ExtTreeMap α β cmp) (a : α) : ExtTreeMap α β cmp :=
  ⟨t.inner.erase a⟩

@[inline, inherit_doc ExtDTreeMap.Const.get?]
def get? [TransCmp cmp] (t : ExtTreeMap α β cmp) (a : α) : Option β :=
  ExtDTreeMap.Const.get? t.inner a

@[inline, inherit_doc ExtDTreeMap.Const.get]
def get [TransCmp cmp] (t : ExtTreeMap α β cmp) (a : α) (h : a ∈ t) : β :=
  ExtDTreeMap.Const.get t.inner a h

@[inline, inherit_doc ExtDTreeMap.Const.get!]
def get! [TransCmp cmp] [Inhabited β] (t : ExtTreeMap α β cmp) (a : α) : β :=
  ExtDTreeMap.Const.get! t.inner a

@[inline, inherit_doc ExtDTreeMap.Const.getD]
def getD [TransCmp cmp] (t : ExtTreeMap α β cmp) (a : α) (fallback : β) : β :=
  ExtDTreeMap.Const.getD t.inner a fallback

instance [TransCmp cmp] : GetElem? (ExtTreeMap α β cmp) α β (fun m a => a ∈ m) where
  getElem m a h := m.get a h
  getElem? m a := m.get? a
  getElem! m a := m.get! a

@[inline, inherit_doc ExtDTreeMap.getKey?]
def getKey? [TransCmp cmp] (t : ExtTreeMap α β cmp) (a : α) : Option α :=
  t.inner.getKey? a

@[inline, inherit_doc ExtDTreeMap.getKey]
def getKey [TransCmp cmp] (t : ExtTreeMap α β cmp) (a : α) (h : a ∈ t) : α :=
  t.inner.getKey a h

@[inline, inherit_doc ExtDTreeMap.getKey!]
def getKey! [TransCmp cmp] [Inhabited α] (t : ExtTreeMap α β cmp) (a : α) : α :=
  t.inner.getKey! a

@[inline, inherit_doc ExtDTreeMap.getKeyD]
def getKeyD [TransCmp cmp] (t : ExtTreeMap α β cmp) (a : α) (fallback : α) : α :=
  t.inner.getKeyD a fallback

@[inline, inherit_doc ExtDTreeMap.Const.minEntry?]
def minEntry? [TransCmp cmp] (t : ExtTreeMap α β cmp) : Option (α × β) :=
  ExtDTreeMap.Const.minEntry? t.inner

@[inline, inherit_doc ExtDTreeMap.Const.minEntry]
def minEntry [TransCmp cmp] (t : ExtTreeMap α β cmp) (h : t ≠ ∅) : α × β :=
  ExtDTreeMap.Const.minEntry t.inner (fun _ => nomatch t)

@[inline, inherit_doc ExtDTreeMap.Const.minEntry!]
def minEntry! [TransCmp cmp] [Inhabited (α × β)] (t : ExtTreeMap α β cmp) : α × β :=
  ExtDTreeMap.Const.minEntry! t.inner

@[inline, inherit_doc ExtDTreeMap.Const.minEntryD]
def minEntryD [TransCmp cmp] (t : ExtTreeMap α β cmp) (fallback : α × β) : α × β :=
  ExtDTreeMap.Const.minEntryD t.inner fallback

@[inline, inherit_doc ExtDTreeMap.Const.maxEntry?]
def maxEntry? [TransCmp cmp] (t : ExtTreeMap α β cmp) : Option (α × β) :=
  ExtDTreeMap.Const.maxEntry? t.inner

@[inline, inherit_doc ExtDTreeMap.Const.maxEntry]
def maxEntry [TransCmp cmp] (t : ExtTreeMap α β cmp) (h : t ≠ ∅) : α × β :=
  ExtDTreeMap.Const.maxEntry t.inner (fun _ => nomatch t)

@[inline, inherit_doc ExtDTreeMap.Const.maxEntry!]
def maxEntry! [TransCmp cmp] [Inhabited (α × β)] (t : ExtTreeMap α β cmp) : α × β :=
  ExtDTreeMap.Const.maxEntry! t.inner

@[inline, inherit_doc ExtDTreeMap.Const.maxEntryD]
def maxEntryD [TransCmp cmp] (t : ExtTreeMap α β cmp) (fallback : α × β) : α × β :=
  ExtDTreeMap.Const.maxEntryD t.inner fallback

@[inline, inherit_doc ExtDTreeMap.minKey?]
def minKey? [TransCmp cmp] (t : ExtTreeMap α β cmp) : Option α :=
  ExtDTreeMap.minKey? t.inner

@[inline, inherit_doc ExtDTreeMap.minKey]
def minKey [TransCmp cmp] (t : ExtTreeMap α β cmp) (h : t ≠ ∅) : α :=
  ExtDTreeMap.minKey t.inner (fun _ => nomatch t)

@[inline, inherit_doc ExtDTreeMap.minKey!]
def minKey! [TransCmp cmp] [Inhabited α] (t : ExtTreeMap α β cmp) : α :=
  ExtDTreeMap.minKey! t.inner

@[inline, inherit_doc ExtDTreeMap.minKeyD]
def minKeyD [TransCmp cmp] (t : ExtTreeMap α β cmp) (fallback : α) : α :=
  ExtDTreeMap.minKeyD t.inner fallback

@[inline, inherit_doc ExtDTreeMap.maxKey?]
def maxKey? [TransCmp cmp] (t : ExtTreeMap α β cmp) : Option α :=
  ExtDTreeMap.maxKey? t.inner

@[inline, inherit_doc ExtDTreeMap.maxKey]
def maxKey [TransCmp cmp] (t : ExtTreeMap α β cmp) (h : t ≠ ∅) : α :=
  ExtDTreeMap.maxKey t.inner (fun _ => nomatch t)

@[inline, inherit_doc ExtDTreeMap.maxKey!]
def maxKey! [TransCmp cmp] [Inhabited α] (t : ExtTreeMap α β cmp) : α :=
  ExtDTreeMap.maxKey! t.inner

@[inline, inherit_doc ExtDTreeMap.maxKeyD]
def maxKeyD [TransCmp cmp] (t : ExtTreeMap α β cmp) (fallback : α) : α :=
  ExtDTreeMap.maxKeyD t.inner fallback

@[inline, inherit_doc ExtDTreeMap.Const.entryAtIdx?]
def entryAtIdx? [TransCmp cmp] (t : ExtTreeMap α β cmp) (n : Nat) : Option (α × β) :=
  ExtDTreeMap.Const.entryAtIdx? t.inner n

@[inline, inherit_doc ExtDTreeMap.Const.entryAtIdx]
def entryAtIdx [TransCmp cmp] (t : ExtTreeMap α β cmp) (n : Nat) (h : n < t.size) : α × β :=
  ExtDTreeMap.Const.entryAtIdx t.inner n h

@[inline, inherit_doc ExtDTreeMap.Const.entryAtIdx!]
def entryAtIdx! [TransCmp cmp] [Inhabited (α × β)] (t : ExtTreeMap α β cmp) (n : Nat) : α × β :=
  ExtDTreeMap.Const.entryAtIdx! t.inner n

@[inline, inherit_doc ExtDTreeMap.Const.entryAtIdxD]
def entryAtIdxD [TransCmp cmp] (t : ExtTreeMap α β cmp) (n : Nat) (fallback : α × β) : α × β :=
  ExtDTreeMap.Const.entryAtIdxD t.inner n fallback

@[inline, inherit_doc ExtDTreeMap.keyAtIdx?]
def keyAtIdx? [TransCmp cmp] (t : ExtTreeMap α β cmp) (n : Nat) : Option α :=
  ExtDTreeMap.keyAtIdx? t.inner n

@[inline, inherit_doc ExtDTreeMap.keyAtIdx]
def keyAtIdx [TransCmp cmp] (t : ExtTreeMap α β cmp) (n : Nat) (h : n < t.size) : α :=
  ExtDTreeMap.keyAtIdx t.inner n h

@[inline, inherit_doc ExtDTreeMap.keyAtIdx!]
def keyAtIdx! [TransCmp cmp] [Inhabited α] (t : ExtTreeMap α β cmp) (n : Nat) : α :=
  ExtDTreeMap.keyAtIdx! t.inner n

@[inline, inherit_doc ExtDTreeMap.keyAtIdxD]
def keyAtIdxD [TransCmp cmp] (t : ExtTreeMap α β cmp) (n : Nat) (fallback : α) : α :=
  ExtDTreeMap.keyAtIdxD t.inner n fallback

@[inline, inherit_doc ExtDTreeMap.Const.getEntryGE?]
def getEntryGE? [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) : Option (α × β) :=
  ExtDTreeMap.Const.getEntryGE? t.inner k

@[inline, inherit_doc ExtDTreeMap.Const.getEntryGT?]
def getEntryGT? [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) : Option (α × β) :=
  ExtDTreeMap.Const.getEntryGT? t.inner k

@[inline, inherit_doc ExtDTreeMap.Const.getEntryLE?]
def getEntryLE? [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) : Option (α × β) :=
  ExtDTreeMap.Const.getEntryLE? t.inner k

@[inline, inherit_doc ExtDTreeMap.Const.getEntryLT?]
def getEntryLT? [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) : Option (α × β) :=
  ExtDTreeMap.Const.getEntryLT? t.inner k

@[inline, inherit_doc ExtDTreeMap.Const.getEntryGE]
def getEntryGE [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isGE) :
    α × β :=
  ExtDTreeMap.Const.getEntryGE t.inner k h

@[inline, inherit_doc DTreeMap.Const.getEntryGT]
def getEntryGT [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .gt) :
    α × β :=
  ExtDTreeMap.Const.getEntryGT t.inner k h

@[inline, inherit_doc DTreeMap.Const.getEntryLE]
def getEntryLE [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isLE) :
    α × β :=
  ExtDTreeMap.Const.getEntryLE t.inner k h

@[inline, inherit_doc DTreeMap.Const.getEntryLT]
def getEntryLT [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .lt) :
    α × β :=
  ExtDTreeMap.Const.getEntryLT t.inner k h

@[inline, inherit_doc ExtDTreeMap.Const.getEntryGE!]
def getEntryGE! [TransCmp cmp] [Inhabited (α × β)] (t : ExtTreeMap α β cmp) (k : α) : (α × β) :=
  ExtDTreeMap.Const.getEntryGE! t.inner k

@[inline, inherit_doc ExtDTreeMap.Const.getEntryGT!]
def getEntryGT! [TransCmp cmp] [Inhabited (α × β)] (t : ExtTreeMap α β cmp) (k : α) : (α × β) :=
  ExtDTreeMap.Const.getEntryGT! t.inner k

@[inline, inherit_doc ExtDTreeMap.Const.getEntryLE!]
def getEntryLE! [TransCmp cmp] [Inhabited (α × β)] (t : ExtTreeMap α β cmp) (k : α) : (α × β) :=
  ExtDTreeMap.Const.getEntryLE! t.inner k

@[inline, inherit_doc ExtDTreeMap.Const.getEntryLT!]
def getEntryLT! [TransCmp cmp] [Inhabited (α × β)] (t : ExtTreeMap α β cmp) (k : α) : (α × β) :=
  ExtDTreeMap.Const.getEntryLT! t.inner k

@[inline, inherit_doc ExtDTreeMap.Const.getEntryGED]
def getEntryGED [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) (fallback : α × β) : (α × β) :=
  ExtDTreeMap.Const.getEntryGED t.inner k fallback

@[inline, inherit_doc ExtDTreeMap.Const.getEntryGTD]
def getEntryGTD [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) (fallback : α × β) : (α × β) :=
  ExtDTreeMap.Const.getEntryGTD t.inner k fallback

@[inline, inherit_doc ExtDTreeMap.Const.getEntryLED]
def getEntryLED [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) (fallback : α × β) : (α × β) :=
  ExtDTreeMap.Const.getEntryLED t.inner k fallback

@[inline, inherit_doc ExtDTreeMap.Const.getEntryLTD]
def getEntryLTD [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) (fallback : α × β) : (α × β) :=
  ExtDTreeMap.Const.getEntryLTD t.inner k fallback

@[inline, inherit_doc ExtDTreeMap.getKeyGE?]
def getKeyGE? [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) : Option α :=
  ExtDTreeMap.getKeyGE? t.inner k

@[inline, inherit_doc ExtDTreeMap.getKeyGT?]
def getKeyGT? [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) : Option α :=
  ExtDTreeMap.getKeyGT? t.inner k

@[inline, inherit_doc ExtDTreeMap.getKeyLE?]
def getKeyLE? [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) : Option α :=
  ExtDTreeMap.getKeyLE? t.inner k

@[inline, inherit_doc ExtDTreeMap.getKeyLT?]
def getKeyLT? [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) : Option α :=
  ExtDTreeMap.getKeyLT? t.inner k

@[inline, inherit_doc ExtDTreeMap.getKeyGE]
def getKeyGE [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isGE) : α :=
  ExtDTreeMap.getKeyGE t.inner k h

@[inline, inherit_doc ExtDTreeMap.getKeyGT]
def getKeyGT [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .gt) : α :=
  ExtDTreeMap.getKeyGT t.inner k h

@[inline, inherit_doc ExtDTreeMap.getKeyLE]
def getKeyLE [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isLE) : α :=
  ExtDTreeMap.getKeyLE t.inner k h

@[inline, inherit_doc ExtDTreeMap.getKeyLT]
def getKeyLT [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .lt) : α :=
  ExtDTreeMap.getKeyLT t.inner k h

@[inline, inherit_doc ExtDTreeMap.getKeyGE!]
def getKeyGE! [TransCmp cmp] [Inhabited α] (t : ExtTreeMap α β cmp) (k : α) : α :=
  ExtDTreeMap.getKeyGE! t.inner k

@[inline, inherit_doc ExtDTreeMap.getKeyGT!]
def getKeyGT! [TransCmp cmp] [Inhabited α] (t : ExtTreeMap α β cmp) (k : α) : α :=
  ExtDTreeMap.getKeyGT! t.inner k

@[inline, inherit_doc ExtDTreeMap.getKeyLE!]
def getKeyLE! [TransCmp cmp] [Inhabited α] (t : ExtTreeMap α β cmp) (k : α) : α :=
  ExtDTreeMap.getKeyLE! t.inner k

@[inline, inherit_doc ExtDTreeMap.getKeyLT!]
def getKeyLT! [TransCmp cmp] [Inhabited α] (t : ExtTreeMap α β cmp) (k : α) : α :=
  ExtDTreeMap.getKeyLT! t.inner k

@[inline, inherit_doc ExtDTreeMap.getKeyGED]
def getKeyGED [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) (fallback : α) : α :=
  ExtDTreeMap.getKeyGED t.inner k fallback

@[inline, inherit_doc ExtDTreeMap.getKeyGTD]
def getKeyGTD [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) (fallback : α) : α :=
  ExtDTreeMap.getKeyGTD t.inner k fallback

@[inline, inherit_doc ExtDTreeMap.getKeyLED]
def getKeyLED [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) (fallback : α) : α :=
  ExtDTreeMap.getKeyLED t.inner k fallback

@[inline, inherit_doc ExtDTreeMap.getKeyLTD]
def getKeyLTD [TransCmp cmp] (t : ExtTreeMap α β cmp) (k : α) (fallback : α) : α :=
  ExtDTreeMap.getKeyLTD t.inner k fallback

variable {δ : Type w} {m : Type w → Type w₂} [Monad m] [LawfulMonad m]

@[inline, inherit_doc ExtDTreeMap.filter]
def filter (f : α → β → Bool) (m : ExtTreeMap α β cmp) : ExtTreeMap α β cmp :=
  ⟨m.inner.filter f⟩

@[inline, inherit_doc ExtDTreeMap.filterMap]
def filterMap (f : (a : α) → β → Option γ) (m : ExtTreeMap α β cmp) : ExtTreeMap α γ cmp :=
  ⟨m.inner.filterMap f⟩

@[inline, inherit_doc ExtDTreeMap.map]
def map (f : α → β → γ) (t : ExtTreeMap α β cmp) : ExtTreeMap α γ cmp :=
  ⟨t.inner.map f⟩

@[inline, inherit_doc ExtDTreeMap.foldlM]
def foldlM [TransCmp cmp] (f : δ → (a : α) → β → m δ) (init : δ) (t : ExtTreeMap α β cmp) : m δ :=
  t.inner.foldlM f init

@[inline, inherit_doc ExtDTreeMap.foldl]
def foldl [TransCmp cmp] (f : δ → (a : α) → β → δ) (init : δ) (t : ExtTreeMap α β cmp) : δ :=
  t.inner.foldl f init

@[inline, inherit_doc ExtDTreeMap.foldrM]
def foldrM [TransCmp cmp] (f : (a : α) → β → δ → m δ) (init : δ) (t : ExtTreeMap α β cmp) : m δ :=
  t.inner.foldrM f init

@[inline, inherit_doc ExtDTreeMap.foldr]
def foldr [TransCmp cmp] (f : (a : α) → β → δ → δ) (init : δ) (t : ExtTreeMap α β cmp) : δ :=
  t.inner.foldr f init

@[inline, inherit_doc ExtDTreeMap.partition]
def partition [TransCmp cmp] (f : (a : α) → β → Bool) (t : ExtTreeMap α β cmp) :
    ExtTreeMap α β cmp × ExtTreeMap α β cmp :=
  let p := t.inner.partition f; (⟨p.1⟩, ⟨p.2⟩)

@[inline, inherit_doc ExtDTreeMap.forM]
def forM [TransCmp cmp] (f : α → β → m PUnit) (t : ExtTreeMap α β cmp) : m PUnit :=
  t.inner.forM f

@[inline, inherit_doc ExtDTreeMap.forIn]
def forIn [TransCmp cmp] (f : α → β → δ → m (ForInStep δ)) (init : δ) (t : ExtTreeMap α β cmp) : m δ :=
  t.inner.forIn (fun a b c => f a b c) init

instance [TransCmp cmp] [Monad m] [LawfulMonad m] : ForM m (ExtTreeMap α β cmp) (α × β) where
  forM t f := forM (fun a b => f ⟨a, b⟩) t

instance [TransCmp cmp] [Monad m] [LawfulMonad m] : ForIn m (ExtTreeMap α β cmp) (α × β) where
  forIn m init f := forIn (fun a b acc => f ⟨a, b⟩ acc) init m

@[inline, inherit_doc ExtDTreeMap.any]
def any [TransCmp cmp] (t : ExtTreeMap α β cmp) (p : α → β → Bool) : Bool :=
  t.inner.any p

@[inline, inherit_doc ExtDTreeMap.all]
def all [TransCmp cmp] (t : ExtTreeMap α β cmp) (p : α → β → Bool) : Bool :=
  t.inner.all p

@[inline, inherit_doc ExtDTreeMap.keys]
def keys [TransCmp cmp] (t : ExtTreeMap α β cmp) : List α :=
  t.inner.keys

@[inline, inherit_doc ExtDTreeMap.keysArray]
def keysArray [TransCmp cmp] (t : ExtTreeMap α β cmp) : Array α :=
  t.inner.keysArray

@[inline, inherit_doc ExtDTreeMap.values]
def values [TransCmp cmp] (t : ExtTreeMap α β cmp) : List β :=
  t.inner.values

@[inline, inherit_doc ExtDTreeMap.valuesArray]
def valuesArray [TransCmp cmp] (t : ExtTreeMap α β cmp) : Array β :=
  t.inner.valuesArray

@[inline, inherit_doc ExtDTreeMap.Const.toList]
def toList [TransCmp cmp] (t : ExtTreeMap α β cmp) : List (α × β) :=
  ExtDTreeMap.Const.toList t.inner

@[inline, inherit_doc ExtDTreeMap.Const.ofList]
def ofList (l : List (α × β)) (cmp : α → α → Ordering := by exact compare) : ExtTreeMap α β cmp :=
  ⟨ExtDTreeMap.Const.ofList l cmp⟩

@[inline, inherit_doc ExtDTreeMap.Const.unitOfList]
def unitOfList (l : List α) (cmp : α → α → Ordering := by exact compare) : ExtTreeMap α Unit cmp :=
  ⟨ExtDTreeMap.Const.unitOfList l cmp⟩

@[inline, inherit_doc ExtDTreeMap.Const.toArray]
def toArray [TransCmp cmp] (t : ExtTreeMap α β cmp) : Array (α × β) :=
  ExtDTreeMap.Const.toArray t.inner

@[inline, inherit_doc ExtDTreeMap.Const.ofArray]
def ofArray (a : Array (α × β)) (cmp : α → α → Ordering := by exact compare) : ExtTreeMap α β cmp :=
  ⟨ExtDTreeMap.Const.ofArray a cmp⟩

@[inline, inherit_doc ExtDTreeMap.Const.unitOfArray]
def unitOfArray (a : Array α) (cmp : α → α → Ordering := by exact compare) : ExtTreeMap α Unit cmp :=
  ⟨ExtDTreeMap.Const.unitOfArray a cmp⟩

@[inline, inherit_doc ExtDTreeMap.Const.modify]
def modify [TransCmp cmp] (t : ExtTreeMap α β cmp) (a : α) (f : β → β) : ExtTreeMap α β cmp :=
  ⟨ExtDTreeMap.Const.modify t.inner a f⟩

@[inline, inherit_doc ExtDTreeMap.Const.alter]
def alter [TransCmp cmp] (t : ExtTreeMap α β cmp) (a : α) (f : Option β → Option β) : ExtTreeMap α β cmp :=
  ⟨ExtDTreeMap.Const.alter t.inner a f⟩

@[inline, inherit_doc ExtDTreeMap.Const.mergeWith]
def mergeWith [TransCmp cmp] (mergeFn : α → β → β → β) (t₁ t₂ : ExtTreeMap α β cmp) : ExtTreeMap α β cmp :=
  ⟨ExtDTreeMap.Const.mergeWith mergeFn t₁.inner t₂.inner⟩

@[inline, inherit_doc ExtDTreeMap.Const.insertMany]
def insertMany [TransCmp cmp] {ρ} [ForIn Id ρ (α × β)] (t : ExtTreeMap α β cmp) (l : ρ) : ExtTreeMap α β cmp :=
  ⟨ExtDTreeMap.Const.insertMany t.inner l⟩

@[inline, inherit_doc ExtDTreeMap.Const.insertManyIfNewUnit]
def insertManyIfNewUnit [TransCmp cmp] {ρ} [ForIn Id ρ α] (t : ExtTreeMap α Unit cmp) (l : ρ) : ExtTreeMap α Unit cmp :=
  ⟨ExtDTreeMap.Const.insertManyIfNewUnit t.inner l⟩

@[inline, inherit_doc ExtDTreeMap.union]
def union [TransCmp cmp] (t₁ t₂ : ExtTreeMap α β cmp) : ExtTreeMap α β cmp := ⟨ExtDTreeMap.union t₁.inner t₂.inner⟩

instance [TransCmp cmp] : Union (ExtTreeMap α β cmp) := ⟨union⟩

@[inline, inherit_doc ExtDTreeMap.inter]
def inter [TransCmp cmp] (t₁ t₂ : ExtTreeMap α β cmp) : ExtTreeMap α β cmp := ⟨ExtDTreeMap.inter t₁.inner t₂.inner⟩

instance [TransCmp cmp] : Inter (ExtTreeMap α β cmp) := ⟨inter⟩

instance [TransCmp cmp] [BEq β] : BEq (ExtTreeMap α β cmp) where
  beq m₁ m₂ := ExtDTreeMap.Const.beq m₁.inner m₂.inner

instance [TransCmp cmp] [BEq β] [ReflBEq β] : ReflBEq (ExtTreeMap α β cmp) where
  rfl := ExtDTreeMap.Const.beq_of_eq _ _ rfl

instance [TransCmp cmp] [LawfulEqCmp cmp] [BEq β] [LawfulBEq β] : LawfulBEq (ExtTreeMap α β cmp) where
  eq_of_beq {a} {b} hyp := by
    have ⟨_⟩ := a
    have ⟨_⟩ := b
    simp only [mk.injEq]
    exact ExtDTreeMap.Const.eq_of_beq _ _ hyp

@[inline, inherit_doc ExtDTreeMap.diff]
def diff [TransCmp cmp] (t₁ t₂ : ExtTreeMap α β cmp) : ExtTreeMap α β cmp := ⟨ExtDTreeMap.diff t₁.inner t₂.inner⟩

instance [TransCmp cmp] : SDiff (ExtTreeMap α β cmp) := ⟨diff⟩

instance {α : Type u} {β : Type v} {cmp : α → α → Ordering} [LawfulEqCmp cmp] [TransCmp cmp] [BEq β] [LawfulBEq β] : DecidableEq (ExtTreeMap α β cmp) :=
  fun _ _ => decidable_of_iff _ beq_iff_eq

@[inline, inherit_doc ExtDTreeMap.eraseMany]
def eraseMany [TransCmp cmp] {ρ} [ForIn Id ρ α] (t : ExtTreeMap α β cmp) (l : ρ) : ExtTreeMap α β cmp :=
  ⟨t.inner.eraseMany l⟩

instance [TransCmp cmp] [Repr α] [Repr β] : Repr (ExtTreeMap α β cmp) where
  reprPrec m prec := Repr.addAppParen ("Std.ExtTreeMap.ofList " ++ repr m.toList) prec

end ExtTreeMap

end Std
