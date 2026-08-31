/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Std.Data.ExtDHashMap.Basic

@[expose] public section

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# Extensional hash maps

This module develops the type `Std.ExtHashMap` of extensional hash maps. Dependent hash maps
are defined in `Std.Data.ExtDHashMap`.

Lemmas about the operations on `Std.ExtHashMap` are available in the
module `Std.Data.ExtHashMap.Lemmas`.
-/

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w} {_ : BEq α} {_ : Hashable α}

namespace Std

/--
Hash maps.

This is a simple separate-chaining hash table. The data of the hash map consists of a cached size
and an array of buckets, where each bucket is a linked list of key-value pairs. The number of buckets
is always a power of two. The hash map doubles its size upon inserting an element such that the
number of elements is more than 75% of the number of buckets.

The hash table is backed by an `Array`. Users should make sure that the hash map is used linearly to
avoid expensive copies.

The hash map uses `==` (provided by the `BEq` typeclass) to compare keys and `hash` (provided by
the `Hashable` typeclass) to hash them. To ensure that the operations behave as expected, `==`
should be an equivalence relation and `a == b` should imply `hash a = hash b` (see also the
`EquivBEq` and `LawfulHashable` typeclasses). Both of these conditions are automatic if the BEq
instance is lawful, i.e., if `a == b` implies `a = b`.

In contrast to regular hash maps, `Std.ExtHashMap` offers several extensionality lemmas
and therefore has more lemmas about equality of hash maps. This however also makes it lose the
ability to iterate freely over hash maps.

These hash maps contain a bundled well-formedness invariant, which means that they cannot
be used in nested inductive types. For these use cases, `Std.HashMap.Raw` and
`Std.HashMap.Raw.WF` unbundle the invariant from the hash map. When in doubt, prefer
`HashMap` or `ExtHashMap` over `HashMap.Raw`.

Dependent hash maps, in which keys may occur in their values' types, are available as
`Std.ExtDHashMap` in the module `Std.Data.ExtDHashMap`.
-/
structure ExtHashMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  /-- Internal implementation detail of the hash map -/
  inner : ExtDHashMap α (fun _ => β)

namespace ExtHashMap

@[inline, inherit_doc ExtDHashMap.emptyWithCapacity]
def emptyWithCapacity [BEq α] [Hashable α] (capacity := 8) :
    ExtHashMap α β :=
  ⟨ExtDHashMap.emptyWithCapacity capacity⟩

instance [BEq α] [Hashable α] : EmptyCollection (ExtHashMap α β) where
  emptyCollection := emptyWithCapacity

instance [BEq α] [Hashable α] : Inhabited (ExtHashMap α β) where
  default := ∅

@[inline, inherit_doc ExtDHashMap.insert]
def insert [EquivBEq α] [LawfulHashable α] (m : ExtHashMap α β) (a : α)
    (b : β) : ExtHashMap α β :=
  ⟨m.inner.insert a b⟩

instance [EquivBEq α] [LawfulHashable α] : Singleton (α × β) (ExtHashMap α β) where
  singleton | ⟨a, b⟩ => (∅ : ExtHashMap α β).insert a b

instance [EquivBEq α] [LawfulHashable α] : Insert (α × β) (ExtHashMap α β) where
  insert | ⟨a, b⟩, s => s.insert a b

instance [EquivBEq α] [LawfulHashable α] : LawfulSingleton (α × β) (ExtHashMap α β) :=
  ⟨fun _ => rfl⟩

@[inline, inherit_doc ExtDHashMap.insertIfNew]
def insertIfNew [EquivBEq α] [LawfulHashable α] (m : ExtHashMap α β)
    (a : α) (b : β) : ExtHashMap α β :=
  ⟨m.inner.insertIfNew a b⟩

@[inline, inherit_doc ExtDHashMap.containsThenInsert]
def containsThenInsert [EquivBEq α] [LawfulHashable α]
    (m : ExtHashMap α β) (a : α) (b : β) : Bool × ExtHashMap α β :=
  let ⟨replaced, r⟩ := m.inner.containsThenInsert a b
  ⟨replaced, ⟨r⟩⟩

@[inline, inherit_doc ExtDHashMap.containsThenInsertIfNew]
def containsThenInsertIfNew [EquivBEq α] [LawfulHashable α]
    (m : ExtHashMap α β) (a : α) (b : β) : Bool × ExtHashMap α β :=
  let ⟨replaced, r⟩ := m.inner.containsThenInsertIfNew a b
  ⟨replaced, ⟨r⟩⟩

/--
Checks whether a key is present in a map, returning the associated value, and inserts a value for
the key if it was not found.

If the returned value is `some v`, then the returned map is unaltered. If it is `none`, then the
returned map has a new value inserted.

Equivalent to (but potentially faster than) calling `get?` followed by `insertIfNew`.
-/
@[inline]
def getThenInsertIfNew? [EquivBEq α] [LawfulHashable α] (m : ExtHashMap α β) (a : α) (b : β) :
    Option β × ExtHashMap α β :=
  let ⟨previous, r⟩ := ExtDHashMap.Const.getThenInsertIfNew? m.inner a b
  ⟨previous, ⟨r⟩⟩

/--
The notation `m[a]?` is preferred over calling this function directly.

Tries to retrieve the mapping for the given key, returning `none` if no such mapping is present.
-/
@[inline] def get? [EquivBEq α] [LawfulHashable α] (m : ExtHashMap α β) (a : α) : Option β :=
  ExtDHashMap.Const.get? m.inner a

@[inline, inherit_doc ExtDHashMap.contains]
def contains [EquivBEq α] [LawfulHashable α] (m : ExtHashMap α β)
    (a : α) : Bool :=
  m.inner.contains a

instance [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : Membership α (ExtHashMap α β) where
  mem m a := a ∈ m.inner

instance [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : ExtHashMap α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.inner))

/--
The notation `m[a]` or `m[a]'h` is preferred over calling this function directly.

Retrieves the mapping for the given key. Ensures that such a mapping exists by requiring a proof of
`a ∈ m`.
-/
@[inline] def get [EquivBEq α] [LawfulHashable α] (m : ExtHashMap α β) (a : α) (h : a ∈ m) : β :=
  ExtDHashMap.Const.get m.inner a h

@[inline, inherit_doc ExtDHashMap.Const.getD]
def getD [EquivBEq α] [LawfulHashable α] (m : ExtHashMap α β) (a : α)
    (fallback : β) : β :=
  ExtDHashMap.Const.getD m.inner a fallback

/--
The notation `m[a]!` is preferred over calling this function directly.

Tries to retrieve the mapping for the given key, panicking if no such mapping is present.
-/
@[inline]
def get! [EquivBEq α] [LawfulHashable α] [Inhabited β] (m : ExtHashMap α β) (a : α) : β :=
  ExtDHashMap.Const.get! m.inner a

instance [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] :
    GetElem? (ExtHashMap α β) α β (fun m a => a ∈ m) where
  getElem m a h := m.get a h
  getElem? m a := m.get? a
  getElem! m a := m.get! a

@[inline, inherit_doc ExtDHashMap.getKey?]
def getKey? [EquivBEq α] [LawfulHashable α] (m : ExtHashMap α β) (a : α) : Option α :=
  ExtDHashMap.getKey? m.inner a

@[inline, inherit_doc ExtDHashMap.getKey]
def getKey [EquivBEq α] [LawfulHashable α] (m : ExtHashMap α β) (a : α) (h : a ∈ m) : α :=
  ExtDHashMap.getKey m.inner a h

@[inline, inherit_doc ExtDHashMap.getKeyD]
def getKeyD [EquivBEq α] [LawfulHashable α] (m : ExtHashMap α β) (a : α) (fallback : α) : α :=
  ExtDHashMap.getKeyD m.inner a fallback

@[inline, inherit_doc ExtDHashMap.getKey!]
def getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] (m : ExtHashMap α β) (a : α) : α :=
  ExtDHashMap.getKey! m.inner a

@[inline, inherit_doc ExtDHashMap.erase]
def erase [EquivBEq α] [LawfulHashable α] (m : ExtHashMap α β) (a : α) :
    ExtHashMap α β :=
  ⟨m.inner.erase a⟩

@[inline, inherit_doc ExtDHashMap.size]
def size [EquivBEq α] [LawfulHashable α] (m : ExtHashMap α β) : Nat :=
  m.inner.size

@[inline, inherit_doc ExtDHashMap.isEmpty]
def isEmpty [EquivBEq α] [LawfulHashable α] (m : ExtHashMap α β) : Bool :=
  m.inner.isEmpty

@[inline, inherit_doc ExtDHashMap.Const.ofList]
def ofList [BEq α] [Hashable α] (l : List (α × β)) :
    ExtHashMap α β :=
  ⟨ExtDHashMap.Const.ofList l⟩

@[inline, inherit_doc ExtDHashMap.Const.unitOfList]
def unitOfList [BEq α] [Hashable α] (l : List α) :
    ExtHashMap α Unit :=
  ⟨ExtDHashMap.Const.unitOfList l⟩

@[inline, inherit_doc ExtDHashMap.filter]
def filter [EquivBEq α] [LawfulHashable α] (f : α → β → Bool)
    (m : ExtHashMap α β) : ExtHashMap α β :=
  ⟨m.inner.filter f⟩

@[inline, inherit_doc ExtDHashMap.map]
def map [EquivBEq α] [LawfulHashable α] (f : α → β → γ)
    (m : ExtHashMap α β) : ExtHashMap α γ :=
  ⟨m.inner.map f⟩

@[inline, inherit_doc ExtDHashMap.filterMap]
def filterMap [EquivBEq α] [LawfulHashable α] (f : α → β → Option γ)
    (m : ExtHashMap α β) : ExtHashMap α γ :=
  ⟨m.inner.filterMap f⟩

@[inline, inherit_doc ExtDHashMap.modify]
def modify [EquivBEq α] [LawfulHashable α] (m : ExtHashMap α β) (a : α) (f : β → β) :
    ExtHashMap α β :=
  ⟨ExtDHashMap.Const.modify m.inner a f⟩

@[inline, inherit_doc ExtDHashMap.alter]
def alter [EquivBEq α] [LawfulHashable α] (m : ExtHashMap α β) (a : α)
    (f : Option β → Option β) : ExtHashMap α β :=
  ⟨ExtDHashMap.Const.alter m.inner a f⟩

@[inline, inherit_doc ExtDHashMap.Const.insertMany]
def insertMany [EquivBEq α] [LawfulHashable α] {ρ : Type w}
    [ForIn Id ρ (α × β)] (m : ExtHashMap α β) (l : ρ) : ExtHashMap α β :=
  ⟨ExtDHashMap.Const.insertMany m.inner l⟩

@[inline, inherit_doc ExtDHashMap.Const.insertManyIfNewUnit]
def insertManyIfNewUnit [EquivBEq α] [LawfulHashable α]
    {ρ : Type w} [ForIn Id ρ α] (m : ExtHashMap α Unit) (l : ρ) : ExtHashMap α Unit :=
  ⟨ExtDHashMap.Const.insertManyIfNewUnit m.inner l⟩

@[inline, inherit_doc ExtDHashMap.union]
def union [EquivBEq α] [LawfulHashable α] (m₁ m₂ : ExtHashMap α β) : ExtHashMap α β := ⟨ExtDHashMap.union m₁.inner m₂.inner⟩

instance [EquivBEq α] [LawfulHashable α] : Union (ExtHashMap α β) := ⟨union⟩

instance [EquivBEq α] [LawfulHashable α] [BEq β] : BEq (ExtHashMap α β) where
  beq m₁ m₂ := ExtDHashMap.Const.beq m₁.inner m₂.inner

instance [EquivBEq α] [LawfulHashable α] [BEq β] [ReflBEq β] : ReflBEq (ExtHashMap α β) where
  rfl := ExtDHashMap.Const.beq_of_eq _ _ rfl

instance [LawfulBEq α] [BEq β] [LawfulBEq β] : LawfulBEq (ExtHashMap α β) where
  eq_of_beq {a} {b} hyp := by
    have ⟨_⟩ := a
    have ⟨_⟩ := b
    simp only [mk.injEq] at |- hyp
    exact ExtDHashMap.Const.eq_of_beq _ _ hyp

instance {α : Type u} {β : Type v} [BEq α] [LawfulBEq α] [Hashable α] [BEq β] [LawfulBEq β] : DecidableEq (ExtHashMap α β) :=
  fun _ _ => decidable_of_iff _ beq_iff_eq

@[inline, inherit_doc ExtDHashMap.inter]
def inter [EquivBEq α] [LawfulHashable α] (m₁ m₂ : ExtHashMap α β) : ExtHashMap α β := ⟨ExtDHashMap.inter m₁.inner m₂.inner⟩

instance [EquivBEq α] [LawfulHashable α] : Inter (ExtHashMap α β) := ⟨inter⟩

@[inline, inherit_doc ExtDHashMap.diff]
def diff [EquivBEq α] [LawfulHashable α] (m₁ m₂ : ExtHashMap α β) : ExtHashMap α β := ⟨ExtDHashMap.diff m₁.inner m₂.inner⟩

instance [EquivBEq α] [LawfulHashable α] : SDiff (ExtHashMap α β) := ⟨diff⟩

@[inline, inherit_doc ExtDHashMap.Const.unitOfArray]
def unitOfArray [BEq α] [Hashable α] (l : Array α) :
    ExtHashMap α Unit :=
  ⟨ExtDHashMap.Const.unitOfArray l⟩

end Std.ExtHashMap
