/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DHashMap.Raw

set_option linter.missingDocs true
set_option autoImplicit false

/-
# Hash maps with unbundled well-formedness invariant

This module develops the type `Std.Data.HashMap.Raw` of dependent hash maps with unbundled
well-formedness invariant.

This version is safe to use in nested inductive types. The well-formedness predicate is
available as `Std.Data.HashMap.Raw.WF` and we prove in this file that all operations preserve
well-formedness. When in doubt, prefer `HashMap` over `DHashMap.Raw`.

Lemmas about the operations on `Std.Data.HashMap.Raw` are available in the module
`Std.Data.HashMap.RawLemmas`.
-/

universe u v w

variable {α : Type u} {β : Type v}

namespace Std

namespace HashMap

/--
Hash maps without a bundled well-formedness invariant, suitable for use in nested
inductive types. The well-formedness invariant is called `Raw.WF`. When in doubt, prefer `HashMap`
over `HashMap.Raw`. Lemmas about the operations on `Std.Data.HashMap.Raw` are available in the
module `Std.Data.HashMap.RawLemmas`.

This is a simple separate-chaining hash table. The data of the hash map consists of a cached size
and an array of buckets, where each bucket is a linked list of key-value pais. The number of buckets
is always a power of two. The hash map doubles its size upon inserting an element such that the
number of elements is more than 75% of the number of buckets.

The hash table is backed by an `Array`. Users should make sure that the hash map is used linearly to
avoid expensive copies.

The hash map uses `==` (provided by the `BEq` typeclass) to compare keys and `hash` (provided by
the `Hashable` typeclass) to hash them. To ensure that the operations behave as expected, `==`
should be an equivalence relation and `a == b` should imply `hash a = hash b` (see also the
`EquivBEq` and `LawfulHashable` typeclasses). Both of these conditions are automatic if the BEq
instance is lawful, i.e., if `a == b` implies `a = b`.

Dependent hash maps, in which keys may occur in their values' types, are available as
`Std.Data.Raw.DHashMap`.
-/
structure Raw (α : Type u) (β : Type v) where
  /-- Internal implementation detail of the hash map -/
  inner : DHashMap.Raw α (fun _ => β)

namespace Raw

@[inline, inherit_doc DHashMap.Raw.empty] def empty (capacity := 8) : Raw α β :=
  ⟨DHashMap.Raw.empty capacity⟩

instance : EmptyCollection (Raw α β) where
  emptyCollection := empty

instance : Inhabited (Raw α β) where
  default := ∅

set_option linter.unusedVariables false in
@[inline, inherit_doc DHashMap.Raw.insert] def insert [beq : BEq α] [Hashable α] (m : Raw α β)
    (a : α) (b : β) : Raw α β :=
  ⟨m.inner.insert a b⟩

instance [BEq α] [Hashable α] : Singleton (α × β) (Raw α β) := ⟨fun ⟨a, b⟩ => Raw.empty.insert a b⟩

instance [BEq α] [Hashable α] : Insert (α × β) (Raw α β) := ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance [BEq α] [Hashable α] : LawfulSingleton (α × β) (Raw α β) := ⟨fun _ => rfl⟩

@[inline, inherit_doc DHashMap.Raw.insertIfNew] def insertIfNew [BEq α] [Hashable α] (m : Raw α β)
    (a : α) (b : β) : Raw α β :=
  ⟨m.inner.insertIfNew a b⟩

@[inline, inherit_doc DHashMap.Raw.containsThenInsert] def containsThenInsert [BEq α] [Hashable α]
    (m : Raw α β) (a : α) (b : β) : Bool × Raw α β :=
  let ⟨replaced, r⟩ := m.inner.containsThenInsert a b
  ⟨replaced, ⟨r⟩⟩

@[inline, inherit_doc DHashMap.Raw.containsThenInsertIfNew] def containsThenInsertIfNew [BEq α]
    [Hashable α] (m : Raw α β) (a : α) (b : β) : Bool × Raw α β :=
  let ⟨replaced, r⟩ := m.inner.containsThenInsertIfNew a b
  ⟨replaced, ⟨r⟩⟩

/-- Equivalent to (but potentially faster than) calling `get?` followed by `insertIfNew`. -/
@[inline] def getThenInsertIfNew? [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β) :
    Option β × Raw α β :=
  let ⟨previous, r⟩ := DHashMap.Raw.Const.getThenInsertIfNew? m.inner a b
  ⟨previous, ⟨r⟩⟩

set_option linter.unusedVariables false in
/--
The notation `m[a]?` is preferred over calling this function directly.

Tries to retrieve the mapping for the given key, returning `none` if no such mapping is present.
-/
@[inline] def get? [beq : BEq α] [Hashable α] (m : Raw α β) (a : α) : Option β :=
  DHashMap.Raw.Const.get? m.inner a

@[inline, inherit_doc DHashMap.Raw.contains] def contains [BEq α] [Hashable α] (m : Raw α β)
    (a : α) : Bool :=
  m.inner.contains a

instance [BEq α] [Hashable α] : Membership α (Raw α β) where
  mem m a := a ∈ m.inner

instance [BEq α] [Hashable α] {m : Raw α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.inner))

/--
The notation `m[a]` or `m[a]'h` is preferred over calling this function directly.

Retrieves the mapping for the given key. Ensures that such a mapping exists by requiring a proof of
`a ∈ m`.
-/
@[inline] def get [BEq α] [Hashable α] (m : Raw α β) (a : α) (h : a ∈ m) : β :=
  DHashMap.Raw.Const.get m.inner a h

@[inline, inherit_doc DHashMap.Raw.Const.getD] def getD [BEq α] [Hashable α] (m : Raw α β) (a : α)
    (fallback : β) : β := DHashMap.Raw.Const.getD m.inner a fallback

/--
The notation `m[a]!` is preferred over calling this function directly.

Tries to retrieve the mapping for the given key, panicking if no such mapping is present.
-/
@[inline] def get! [BEq α] [Hashable α] [Inhabited β] (m : Raw α β) (a : α) : β :=
  DHashMap.Raw.Const.get! m.inner a

instance [BEq α] [Hashable α] : GetElem? (Raw α β) α β (fun m a => a ∈ m) where
  getElem m a h := m.get a h
  getElem? m a := m.get? a
  getElem! m a := m.get! a

@[inline, inherit_doc DHashMap.Raw.getKey?] def getKey? [BEq α] [Hashable α] (m : Raw α β) (a : α) :
    Option α :=
  DHashMap.Raw.getKey? m.inner a

@[inline, inherit_doc DHashMap.Raw.getKey] def getKey [BEq α] [Hashable α] (m : Raw α β) (a : α)
    (h : a ∈ m) : α :=
  DHashMap.Raw.getKey m.inner a h

@[inline, inherit_doc DHashMap.Raw.getKeyD] def getKeyD [BEq α] [Hashable α] (m : Raw α β) (a : α)
    (fallback : α) : α :=
  DHashMap.Raw.getKeyD m.inner a fallback

@[inline, inherit_doc DHashMap.Raw.getKey!] def getKey! [BEq α] [Hashable α] [Inhabited α]
    (m : Raw α β) (a : α) : α :=
  DHashMap.Raw.getKey! m.inner a

@[inline, inherit_doc DHashMap.Raw.erase] def erase [BEq α] [Hashable α] (m : Raw α β)
    (a : α) : Raw α β :=
  ⟨m.inner.erase a⟩

@[inline, inherit_doc DHashMap.Raw.size] def size (m : Raw α β) : Nat :=
  m.inner.size

@[inline, inherit_doc DHashMap.Raw.isEmpty] def isEmpty (m : Raw α β) : Bool :=
  m.inner.isEmpty

@[inline, inherit_doc DHashMap.Raw.keys] def keys (m : Raw α β) : List α :=
  m.inner.keys

section Unverified

/-! We currently do not provide lemmas for the functions below. -/

@[inline, inherit_doc DHashMap.Raw.filterMap] def filterMap {γ : Type w} (f : α → β → Option γ)
    (m : Raw α β) : Raw α γ :=
  ⟨m.inner.filterMap f⟩

@[inline, inherit_doc DHashMap.Raw.map] def map {γ : Type w} (f : α → β → γ) (m : Raw α β) :
    Raw α γ :=
  ⟨m.inner.map f⟩

@[inline, inherit_doc DHashMap.Raw.filter] def filter (f : α → β → Bool) (m : Raw α β) : Raw α β :=
  ⟨m.inner.filter f⟩

@[inline, inherit_doc DHashMap.Raw.foldM] def foldM {m : Type w → Type w} [Monad m] {γ : Type w}
    (f : γ → α → β → m γ) (init : γ) (b : Raw α β) : m γ :=
  b.inner.foldM f init

@[inline, inherit_doc DHashMap.Raw.fold] def fold {γ : Type w} (f : γ → α → β → γ) (init : γ)
    (b : Raw α β) : γ :=
  b.inner.fold f init

@[inline, inherit_doc DHashMap.Raw.forM] def forM {m : Type w → Type w} [Monad m]
    (f : (a : α) → β → m PUnit) (b : Raw α β) : m PUnit :=
  b.inner.forM f

@[inline, inherit_doc DHashMap.Raw.forIn] def forIn {m : Type w → Type w} [Monad m] {γ : Type w}
    (f : (a : α) → β → γ → m (ForInStep γ)) (init : γ) (b : Raw α β) : m γ :=
  b.inner.forIn f init

instance {m : Type w → Type w} : ForM m (Raw α β) (α × β) where
  forM m f := m.forM (fun a b => f (a, b))

instance {m : Type w → Type w} : ForIn m (Raw α β) (α × β) where
  forIn m init f := m.forIn (fun a b acc => f (a, b) acc) init

@[inline, inherit_doc DHashMap.Raw.Const.toList] def toList (m : Raw α β) : List (α × β) :=
  DHashMap.Raw.Const.toList m.inner

@[inline, inherit_doc DHashMap.Raw.Const.toArray] def toArray (m : Raw α β) : Array (α × β) :=
  DHashMap.Raw.Const.toArray m.inner

@[inline, inherit_doc DHashMap.Raw.keysArray] def keysArray (m : Raw α β) : Array α :=
  m.inner.keysArray

@[inline, inherit_doc DHashMap.Raw.values] def values (m : Raw α β) : List β :=
m.inner.values

@[inline, inherit_doc DHashMap.Raw.valuesArray] def valuesArray (m : Raw α β) : Array β :=
  m.inner.valuesArray

@[inline, inherit_doc DHashMap.Raw.Const.insertMany] def insertMany [BEq α] [Hashable α]
    {ρ : Type w} [ForIn Id ρ (α × β)] (m : Raw α β) (l : ρ) : Raw α β :=
  ⟨DHashMap.Raw.Const.insertMany m.inner l⟩

@[inline, inherit_doc DHashMap.Raw.Const.insertManyUnit] def insertManyUnit [BEq α] [Hashable α]
    {ρ : Type w} [ForIn Id ρ α] (m : Raw α Unit) (l : ρ) : Raw α Unit :=
  ⟨DHashMap.Raw.Const.insertManyUnit m.inner l⟩

@[inline, inherit_doc DHashMap.Raw.Const.ofList] def ofList [BEq α] [Hashable α]
    (l : List (α × β)) : Raw α β :=
  ⟨DHashMap.Raw.Const.ofList l⟩

/-- Computes the union of the given hash maps, by traversing `m₂` and inserting its elements into `m₁`. -/
@[inline] def union [BEq α] [Hashable α] (m₁ m₂ : Raw α β) : Raw α β :=
  m₂.fold (init := m₁) fun acc x => acc.insert x

instance [BEq α] [Hashable α] : Union (Raw α β) := ⟨union⟩

@[inline, inherit_doc DHashMap.Raw.Const.unitOfList] def unitOfList [BEq α] [Hashable α]
    (l : List α) : Raw α Unit :=
  ⟨DHashMap.Raw.Const.unitOfList l⟩

@[inline, inherit_doc DHashMap.Raw.Const.unitOfArray] def unitOfArray [BEq α] [Hashable α]
    (l : Array α) : Raw α Unit :=
  ⟨DHashMap.Raw.Const.unitOfArray l⟩

@[inherit_doc DHashMap.Raw.Internal.numBuckets] def Internal.numBuckets (m : Raw α β) : Nat :=
  DHashMap.Raw.Internal.numBuckets m.inner

instance [Repr α] [Repr β] : Repr (Raw α β) where
  reprPrec m prec := Repr.addAppParen ("Std.HashMap.Raw.ofList " ++ reprArg m.toList) prec

end Unverified

/--
Well-formedness predicate for hash maps. Users of `HashMap` will not need to interact with this.
Users of `HashMap.Raw` will need to provide proofs of `WF` to lemmas and should use lemmas
`WF.empty` and `WF.insert` (which are always named exactly like the operations they are about) to
show that map operations preserve well-formedness.
-/
structure WF [BEq α] [Hashable α] (m : Raw α β) : Prop where
  /-- Internal implementation detail of the hash map -/
  out : m.inner.WF

theorem WF.empty [BEq α] [Hashable α] {c} : (empty c : Raw α β).WF :=
  ⟨DHashMap.Raw.WF.empty⟩

theorem WF.emptyc [BEq α] [Hashable α] : (∅ : Raw α β).WF :=
  WF.empty

theorem WF.insert [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β} (h : m.WF) :
    (m.insert a b).WF :=
  ⟨DHashMap.Raw.WF.insert h.out⟩

theorem WF.insertIfNew [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β} (h : m.WF) :
    (m.insertIfNew a b).WF :=
  ⟨DHashMap.Raw.WF.insertIfNew h.out⟩

theorem WF.containsThenInsert [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β} (h : m.WF) :
    (m.containsThenInsert a b).2.WF :=
  ⟨DHashMap.Raw.WF.containsThenInsert h.out⟩

theorem WF.containsThenInsertIfNew [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β} (h : m.WF) :
    (m.containsThenInsertIfNew a b).2.WF :=
  ⟨DHashMap.Raw.WF.containsThenInsertIfNew h.out⟩

theorem WF.getThenInsertIfNew? [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β} (h : m.WF) :
    (m.getThenInsertIfNew? a b).2.WF :=
  ⟨DHashMap.Raw.WF.Const.getThenInsertIfNew? h.out⟩

theorem WF.erase [BEq α] [Hashable α] {m : Raw α β} {a : α} (h : m.WF) : (m.erase a).WF :=
  ⟨DHashMap.Raw.WF.erase h.out⟩

theorem WF.filter [BEq α] [Hashable α] {m : Raw α β} {f : α → β → Bool} (h : m.WF) :
    (m.filter f).WF :=
  ⟨DHashMap.Raw.WF.filter h.out⟩

theorem WF.insertMany [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ (α × β)] {m : Raw α β} {l : ρ}
    (h : m.WF) : (m.insertMany l).WF :=
  ⟨DHashMap.Raw.WF.Const.insertMany h.out⟩

theorem WF.insertManyUnit [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ α] {m : Raw α Unit} {l : ρ}
    (h : m.WF) : (m.insertManyUnit l).WF :=
  ⟨DHashMap.Raw.WF.Const.insertManyUnit h.out⟩

theorem WF.ofList [BEq α] [Hashable α] {l : List (α × β)} : (ofList l).WF :=
  ⟨DHashMap.Raw.WF.Const.ofList⟩

theorem WF.unitOfList [BEq α] [Hashable α] {l : List α} : (unitOfList l).WF :=
  ⟨DHashMap.Raw.WF.Const.unitOfList⟩

end Raw

end HashMap

end Std
