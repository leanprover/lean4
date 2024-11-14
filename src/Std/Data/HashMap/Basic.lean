/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DHashMap.Basic

set_option linter.missingDocs true
set_option autoImplicit false

/-!
# Hash maps

This module develops the type `Std.Data.HashMap` of hash maps. Dependent hash maps are defined in
`Std.Data.DHashMap`.

The operations `map` and `filterMap` on `Std.Data.HashMap` are defined in the module
`Std.Data.HashMap.AdditionalOperations`.

Lemmas about the operations on `Std.Data.HashMap` are available in the
module `Std.Data.HashMap.Lemmas`.

See the module `Std.Data.HashMap.Raw` for a variant of this type which is safe to use in
nested inductive types.
-/

universe u v w

variable {α : Type u} {β : Type v} {_ : BEq α} {_ : Hashable α}

namespace Std

/--
Hash maps.

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

These hash maps contain a bundled well-formedness invariant, which means that they cannot
be used in nested inductive types. For these use cases, `Std.Data.HashMap.Raw` and
`Std.Data.HashMap.Raw.WF` unbundle the invariant from the hash map. When in doubt, prefer
`HashMap` over `HashMap.Raw`.

Dependent hash maps, in which keys may occur in their values' types, are available as
`Std.Data.DHashMap`.
-/
structure HashMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  /-- Internal implementation detail of the hash map -/
  inner : DHashMap α (fun _ => β)

namespace HashMap

@[inline, inherit_doc DHashMap.empty] def empty [BEq α] [Hashable α] (capacity := 8) :
    HashMap α β :=
  ⟨DHashMap.empty capacity⟩

instance [BEq α] [Hashable α] : EmptyCollection (HashMap α β) where
  emptyCollection := empty

instance [BEq α] [Hashable α] : Inhabited (HashMap α β) where
  default := ∅

@[inline, inherit_doc DHashMap.insert] def insert (m : HashMap α β) (a : α)
    (b : β) : HashMap α β :=
  ⟨m.inner.insert a b⟩

instance : Singleton (α × β) (HashMap α β) := ⟨fun ⟨a, b⟩ => HashMap.empty.insert a b⟩

instance : Insert (α × β) (HashMap α β) := ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance : LawfulSingleton (α × β) (HashMap α β) := ⟨fun _ => rfl⟩

@[inline, inherit_doc DHashMap.insertIfNew] def insertIfNew (m : HashMap α β)
    (a : α) (b : β) : HashMap α β :=
  ⟨m.inner.insertIfNew a b⟩

@[inline, inherit_doc DHashMap.containsThenInsert] def containsThenInsert
    (m : HashMap α β) (a : α) (b : β) : Bool × HashMap α β :=
  let ⟨replaced, r⟩ := m.inner.containsThenInsert a b
  ⟨replaced, ⟨r⟩⟩

@[inline, inherit_doc DHashMap.containsThenInsertIfNew] def containsThenInsertIfNew
    (m : HashMap α β) (a : α) (b : β) : Bool × HashMap α β :=
  let ⟨replaced, r⟩ := m.inner.containsThenInsertIfNew a b
  ⟨replaced, ⟨r⟩⟩

/--
Checks whether a key is present in a map, returning the associate value, and inserts a value for
the key if it was not found.

If the returned value is `some v`, then the returned map is unaltered. If it is `none`, then the
returned map has a new value inserted.

Equivalent to (but potentially faster than) calling `get?` followed by `insertIfNew`.
-/
@[inline] def getThenInsertIfNew? (m : HashMap α β) (a : α) (b : β) :
    Option β × HashMap α β :=
  let ⟨previous, r⟩ := DHashMap.Const.getThenInsertIfNew? m.inner a b
  ⟨previous, ⟨r⟩⟩

/--
The notation `m[a]?` is preferred over calling this function directly.

Tries to retrieve the mapping for the given key, returning `none` if no such mapping is present.
-/
@[inline] def get? (m : HashMap α β) (a : α) : Option β :=
  DHashMap.Const.get? m.inner a

@[deprecated get? "Use `m[a]?` or `m.get? a` instead" (since := "2024-08-07"), inherit_doc get?]
def find? (m : HashMap α β) (a : α) : Option β :=
  m.get? a

@[inline, inherit_doc DHashMap.contains] def contains (m : HashMap α β)
    (a : α) : Bool :=
  m.inner.contains a

instance [BEq α] [Hashable α] : Membership α (HashMap α β) where
  mem m a := a ∈ m.inner

instance [BEq α] [Hashable α] {m : HashMap α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.inner))

/--
The notation `m[a]` or `m[a]'h` is preferred over calling this function directly.

Retrieves the mapping for the given key. Ensures that such a mapping exists by requiring a proof of
`a ∈ m`.
-/
@[inline] def get (m : HashMap α β) (a : α) (h : a ∈ m) : β :=
  DHashMap.Const.get m.inner a h

@[inline, inherit_doc DHashMap.Const.getD] def getD (m : HashMap α β) (a : α)
    (fallback : β) : β :=
  DHashMap.Const.getD m.inner a fallback

@[deprecated getD (since := "2024-08-07"), inherit_doc getD]
def findD (m : HashMap α β) (a : α) (fallback : β) : β :=
  m.getD a fallback

/--
The notation `m[a]!` is preferred over calling this function directly.

Tries to retrieve the mapping for the given key, panicking if no such mapping is present.
-/
@[inline] def get! [Inhabited β] (m : HashMap α β) (a : α) : β :=
  DHashMap.Const.get! m.inner a

@[deprecated get! "Use `m[a]!` or `m.get! a` instead" (since := "2024-08-07"), inherit_doc get!]
def find! [Inhabited β] (m : HashMap α β) (a : α) : Option β :=
  m.get! a

instance [BEq α] [Hashable α] : GetElem? (HashMap α β) α β (fun m a => a ∈ m) where
  getElem m a h := m.get a h
  getElem? m a := m.get? a
  getElem! m a := m.get! a

@[inline, inherit_doc DHashMap.getKey?] def getKey? (m : HashMap α β) (a : α) : Option α :=
  DHashMap.getKey? m.inner a

@[inline, inherit_doc DHashMap.getKey] def getKey (m : HashMap α β) (a : α) (h : a ∈ m) : α :=
  DHashMap.getKey m.inner a h

@[inline, inherit_doc DHashMap.getKeyD] def getKeyD (m : HashMap α β) (a : α) (fallback : α) : α :=
  DHashMap.getKeyD m.inner a fallback

@[inline, inherit_doc DHashMap.getKey!] def getKey! [Inhabited α] (m : HashMap α β) (a : α) : α :=
  DHashMap.getKey! m.inner a

@[inline, inherit_doc DHashMap.erase] def erase (m : HashMap α β) (a : α) :
    HashMap α β :=
  ⟨m.inner.erase a⟩

@[inline, inherit_doc DHashMap.size] def size (m : HashMap α β) : Nat :=
  m.inner.size

@[inline, inherit_doc DHashMap.isEmpty] def isEmpty (m : HashMap α β) : Bool :=
  m.inner.isEmpty

@[inline, inherit_doc DHashMap.keys] def keys (m : HashMap α β) : List α :=
  m.inner.keys

section Unverified

/-! We currently do not provide lemmas for the functions below. -/

@[inline, inherit_doc DHashMap.filter] def filter (f : α → β → Bool)
    (m : HashMap α β) : HashMap α β :=
  ⟨m.inner.filter f⟩

@[inline, inherit_doc DHashMap.partition] def partition (f : α → β → Bool)
    (m : HashMap α β) : HashMap α β × HashMap α β :=
  let ⟨l, r⟩ := m.inner.partition f
  ⟨⟨l⟩, ⟨r⟩⟩

@[inline, inherit_doc DHashMap.foldM] def foldM {m : Type w → Type w}
    [Monad m] {γ : Type w} (f : γ → α → β → m γ) (init : γ) (b : HashMap α β) : m γ :=
  b.inner.foldM f init

@[inline, inherit_doc DHashMap.fold] def fold {γ : Type w}
    (f : γ → α → β → γ) (init : γ) (b : HashMap α β) : γ :=
  b.inner.fold f init

@[inline, inherit_doc DHashMap.forM] def forM {m : Type w → Type w} [Monad m]
    (f : (a : α) → β → m PUnit) (b : HashMap α β) : m PUnit :=
  b.inner.forM f

@[inline, inherit_doc DHashMap.forIn] def forIn {m : Type w → Type w} [Monad m]
    {γ : Type w} (f : (a : α) → β → γ → m (ForInStep γ)) (init : γ) (b : HashMap α β) : m γ :=
  b.inner.forIn f init

instance [BEq α] [Hashable α] {m : Type w → Type w} : ForM m (HashMap α β) (α × β) where
  forM m f := m.forM (fun a b => f (a, b))

instance [BEq α] [Hashable α] {m : Type w → Type w} : ForIn m (HashMap α β) (α × β) where
  forIn m init f := m.forIn (fun a b acc => f (a, b) acc) init

@[inline, inherit_doc DHashMap.Const.toList] def toList (m : HashMap α β) :
    List (α × β) :=
  DHashMap.Const.toList m.inner

@[inline, inherit_doc DHashMap.Const.toArray] def toArray (m : HashMap α β) :
    Array (α × β) :=
  DHashMap.Const.toArray m.inner

@[inline, inherit_doc DHashMap.keysArray] def keysArray (m : HashMap α β) :
    Array α :=
  m.inner.keysArray

@[inline, inherit_doc DHashMap.values] def values (m : HashMap α β) : List β :=
  m.inner.values

@[inline, inherit_doc DHashMap.valuesArray] def valuesArray (m : HashMap α β) :
    Array β :=
  m.inner.valuesArray

@[inline, inherit_doc DHashMap.modify] def modify (m : HashMap α β) (a : α) (f : β → β) : HashMap α β :=
  match m.get? a with
  | none => m
  | some b => m.erase a |>.insert a (f b)

@[inline, inherit_doc DHashMap.alter] def alter (m : HashMap α β) (a : α) (f : Option β → Option β) : HashMap α β :=
  match m.get? a with
  | none =>
    match f none with
    | none => m
    | some b => m.insert a b
  | some b =>
    match f (some b) with
    | none => m.erase a
    | some b => m.erase a |>.insert a b

@[inline, inherit_doc DHashMap.Const.insertMany] def insertMany {ρ : Type w}
    [ForIn Id ρ (α × β)] (m : HashMap α β) (l : ρ) : HashMap α β :=
  ⟨DHashMap.Const.insertMany m.inner l⟩

@[inline, inherit_doc DHashMap.Const.insertManyUnit] def insertManyUnit
    {ρ : Type w} [ForIn Id ρ α] (m : HashMap α Unit) (l : ρ) : HashMap α Unit :=
  ⟨DHashMap.Const.insertManyUnit m.inner l⟩

@[inline, inherit_doc DHashMap.Const.ofList] def ofList [BEq α] [Hashable α] (l : List (α × β)) :
    HashMap α β :=
  ⟨DHashMap.Const.ofList l⟩

/-- Computes the union of the given hash maps, by traversing `m₂` and inserting its elements into `m₁`. -/
@[inline] def union [BEq α] [Hashable α] (m₁ m₂ : HashMap α β) : HashMap α β :=
  m₂.fold (init := m₁) fun acc x => acc.insert x

instance [BEq α] [Hashable α] : Union (HashMap α β) := ⟨union⟩

@[inline, inherit_doc DHashMap.Const.unitOfList] def unitOfList [BEq α] [Hashable α] (l : List α) :
    HashMap α Unit :=
  ⟨DHashMap.Const.unitOfList l⟩

@[inline, inherit_doc DHashMap.Const.unitOfArray] def unitOfArray [BEq α] [Hashable α] (l : Array α) :
    HashMap α Unit :=
  ⟨DHashMap.Const.unitOfArray l⟩

@[inline, inherit_doc DHashMap.Internal.numBuckets] def Internal.numBuckets
    (m : HashMap α β) : Nat :=
  DHashMap.Internal.numBuckets m.inner

instance [BEq α] [Hashable α] [Repr α] [Repr β] : Repr (HashMap α β) where
  reprPrec m prec := Repr.addAppParen ("Std.HashMap.ofList " ++ reprArg m.toList) prec

end Unverified

end Std.HashMap

/--
Groups all elements `x`, `y` in `xs` with `key x == key y` into the same array
`(xs.groupByKey key).find! (key x)`. Groups preserve the relative order of elements in `xs`.
-/
def Array.groupByKey [BEq α] [Hashable α] (key : β → α) (xs : Array β)
    : Std.HashMap α (Array β) := Id.run do
  let mut groups := ∅
  for x in xs do
    groups := groups.alter (key x) (·.getD #[] |>.push x)
  return groups

/--
Groups all elements `x`, `y` in `xs` with `key x == key y` into the same list
`(xs.groupByKey key).find! (key x)`. Groups preserve the relative order of elements in `xs`.
-/
def List.groupByKey [BEq α] [Hashable α] (key : β → α) (xs : List β) :
    Std.HashMap α (List β) :=
  xs.foldr (init := ∅) fun x acc => acc.alter (key x) (fun v => x :: v.getD [])
