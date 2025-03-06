/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Data.BEq
import Init.Data.Hashable
import Std.Data.DHashMap.Internal.Defs

/-
# Dependent hash maps with unbundled well-formedness invariant

This file develops the type `Std.DHashMap.Raw` of dependent hash
maps with unbundled well-formedness invariant.

This version is safe to use in nested inductive types. The well-formedness predicate is
available as `Std.Data.DHashMap.Raw.WF` and we prove in this file that all operations preserve
well-formedness. When in doubt, prefer `DHashMap` over `DHashMap.Raw`.

Lemmas about the operations on `Std.Data.DHashMap.Raw` are available in the module
`Std.Data.DHashMap.RawLemmas`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w

variable {α : Type u} {β : α → Type v} {δ : Type w} {m : Type w → Type w} [Monad m]

namespace Std

open DHashMap.Internal DHashMap.Internal.List

namespace DHashMap

namespace Raw

/-!
The type `DHashMap.Raw` itself is defined in the module `Std.Data.DHashmap.RawDef` for import
structure reasons.
-/

/--
Creates a new empty hash map. The optional parameter `capacity` can be supplied to presize the
map so that it can hold the given number of mappings without reallocating. It is also possible to
use the empty collection notations `∅` and `{}` to create an empty hash map with the default
capacity.
-/
@[inline] def empty (capacity := 8) : Raw α β :=
  (Raw₀.empty capacity).1

instance : EmptyCollection (Raw α β) where
  emptyCollection := empty

instance : Inhabited (Raw α β) where
  default := ∅

/--
Inserts the given mapping into the map. If there is already a mapping for the given key, then both
key and value will be replaced.

Note: this replacement behavior is true for `HashMap`, `DHashMap`, `HashMap.Raw` and `DHashMap.Raw`.
The `insert` function on `HashSet` and `HashSet.Raw` behaves differently: it will return the set
unchanged if a matching key is already present.
-/
@[inline] def insert [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β a) : Raw α β :=
  if h : 0 < m.buckets.size then
    (Raw₀.insert ⟨m, h⟩ a b).1
  else m -- will never happen for well-formed inputs

instance [BEq α] [Hashable α] : Singleton ((a : α) × β a) (Raw α β) :=
  ⟨fun ⟨a, b⟩ => Raw.empty.insert a b⟩

instance [BEq α] [Hashable α] : Insert ((a : α) × β a) (Raw α β) :=
  ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance [BEq α] [Hashable α] : LawfulSingleton ((a : α) × β a) (Raw α β) :=
  ⟨fun _ => rfl⟩

/--
If there is no mapping for the given key, inserts the given mapping into the map. Otherwise,
returns the map unaltered.
-/
@[inline] def insertIfNew [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β a) : Raw α β :=
  if h : 0 < m.buckets.size then
    (Raw₀.insertIfNew ⟨m, h⟩ a b).1
  else m -- will never happen for well-formed inputs

/--
Checks whether a key is present in a map, and unconditionally inserts a value for the key.

Equivalent to (but potentially faster than) calling `contains` followed by `insert`.
-/
@[inline] def containsThenInsert [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β a) :
    Bool × Raw α β :=
  if h : 0 < m.buckets.size then
    let ⟨replaced, ⟨r, _⟩⟩ := Raw₀.containsThenInsert ⟨m, h⟩ a b
    ⟨replaced, r⟩
  else (false, m) -- will never happen for well-formed inputs

/--
Checks whether a key is present in a map, returning the associated value, and inserts a value for
the key if it was not found.

If the returned value is `some v`, then the returned map is unaltered. If it is `none`, then the
returned map has a new value inserted.

Equivalent to (but potentially faster than) calling `get?` followed by `insertIfNew`.

Uses the `LawfulBEq` instance to cast the retrieved value to the correct type.
-/
@[inline] def getThenInsertIfNew? [BEq α] [Hashable α] [LawfulBEq α] (m : Raw α β) (a : α)
    (b : β a) : Option (β a) × Raw α β :=
  if h : 0 < m.buckets.size then
    let ⟨previous, ⟨r, _⟩⟩ := Raw₀.getThenInsertIfNew? ⟨m, h⟩ a b
    ⟨previous, r⟩
  else (none, m) -- will never happen for well-formed inputs

/--
Checks whether a key is present in a map and inserts a value for the key if it was not found.

If the returned `Bool` is `true`, then the returned map is unaltered. If the `Bool` is `false`, then
the returned map has a new value inserted.

Equivalent to (but potentially faster than) calling `contains` followed by `insertIfNew`.
-/
@[inline] def containsThenInsertIfNew [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β a) :
    Bool × Raw α β :=
  if h : 0 < m.buckets.size then
    let ⟨previous, ⟨r, _⟩⟩ := Raw₀.containsThenInsertIfNew ⟨m, h⟩ a b
    ⟨previous, r⟩
  else (false, m) -- will never happen for well-formed inputs

/--
Tries to retrieve the mapping for the given key, returning `none` if no such mapping is present.

Uses the `LawfulBEq` instance to cast the retrieved value to the correct type.
-/
@[inline] def get? [BEq α] [LawfulBEq α] [Hashable α] (m : Raw α β) (a : α) : Option (β a) :=
  if h : 0 < m.buckets.size then
    Raw₀.get? ⟨m, h⟩ a
  else none -- will never happen for well-formed inputs

/--
Returns `true` if there is a mapping for the given key. There is also a `Prop`-valued version
of this: `a ∈ m` is equivalent to `m.contains a = true`.

Observe that this is different behavior than for lists: for lists, `∈` uses `=` and `contains` uses
`==` for comparisons, while for hash maps, both use `==`.
-/
@[inline] def contains [BEq α] [Hashable α] (m : Raw α β) (a : α) : Bool :=
  if h : 0 < m.buckets.size then
    Raw₀.contains ⟨m, h⟩ a
  else false -- will never happen for well-formed inputs

instance [BEq α] [Hashable α] : Membership α (Raw α β) where
  mem m a := m.contains a

instance [BEq α] [Hashable α] {m : Raw α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (m.contains a))

/--
Retrieves the mapping for the given key. Ensures that such a mapping exists by requiring a proof
of `a ∈ m`.

Uses the `LawfulBEq` instance to cast the retrieved value to the correct type.
-/
@[inline] def get [BEq α] [Hashable α] [LawfulBEq α] (m : Raw α β) (a : α) (h : a ∈ m) : β a :=
  Raw₀.get ⟨m, by change dite .. = true at h; split at h <;> simp_all⟩ a
    (by change dite .. = true at h; split at h <;> simp_all)

/--
Tries to retrieve the mapping for the given key, returning `fallback` if no such mapping is present.

Uses the `LawfulBEq` instance to cast the retrieved value to the correct type.
-/
@[inline] def getD [BEq α] [Hashable α] [LawfulBEq α] (m : Raw α β) (a : α) (fallback : β a) :
    β a :=
  if h : 0 < m.buckets.size then
    Raw₀.getD ⟨m, h⟩ a fallback
  else fallback -- will never happen for well-formed inputs

/--
Tries to retrieve the mapping for the given key, panicking if no such mapping is present.

Uses the `LawfulBEq` instance to cast the retrieved value to the correct type.
-/
@[inline] def get! [BEq α] [Hashable α] [LawfulBEq α] (m : Raw α β) (a : α) [Inhabited (β a)] :
    β a :=
  if h : 0 < m.buckets.size then
    Raw₀.get! ⟨m, h⟩ a
  else default -- will never happen for well-formed inputs

/-- Removes the mapping for the given key if it exists. -/
@[inline] def erase [BEq α] [Hashable α] (m : Raw α β) (a : α) : Raw α β :=
  if h : 0 < m.buckets.size then
    Raw₀.erase ⟨m, h⟩ a
  else m -- will never happen for well-formed inputs

section

variable {β : Type v}

/--
Tries to retrieve the mapping for the given key, returning `none` if no such mapping is present.
-/
@[inline] def Const.get? [BEq α] [Hashable α] (m : Raw α (fun _ => β)) (a : α) : Option β :=
  if h : 0 < m.buckets.size then
    Raw₀.Const.get? ⟨m, h⟩ a
  else none -- will never happen for well-formed inputs

/--
Retrieves the mapping for the given key. Ensures that such a mapping exists by requiring a proof of
`a ∈ m`.
-/
@[inline] def Const.get [BEq α] [Hashable α] (m : Raw α (fun _ => β)) (a : α) (h : a ∈ m) : β :=
  Raw₀.Const.get ⟨m, by change dite .. = true at h; split at h <;> simp_all⟩ a
    (by change dite .. = true at h; split at h <;> simp_all)

/--
Tries to retrieve the mapping for the given key, returning `fallback` if no such mapping is present.
-/
@[inline] def Const.getD [BEq α] [Hashable α] (m : Raw α (fun _ => β)) (a : α) (fallback : β) : β :=
  if h : 0 < m.buckets.size then
    Raw₀.Const.getD ⟨m, h⟩ a fallback
  else fallback -- will never happen for well-formed inputs

/-- Tries to retrieve the mapping for the given key, panicking if no such mapping is present. -/
@[inline] def Const.get! [BEq α] [Hashable α] [Inhabited β] (m : Raw α (fun _ => β)) (a : α) : β :=
  if h : 0 < m.buckets.size then
    Raw₀.Const.get! ⟨m, h⟩ a
  else default -- will never happen for well-formed inputs

/--
Equivalent to (but potentially faster than) calling `Const.get?` followed by `insertIfNew`.

Checks whether a key is present in a map, returning the associated value, and inserts a value for
the key if it was not found.

If the returned value is `some v`, then the returned map is unaltered. If it is `none`, then the
returned map has a new value inserted.
-/
@[inline] def Const.getThenInsertIfNew? [BEq α] [Hashable α] (m : Raw α (fun _ => β)) (a : α)
    (b : β) : Option β × Raw α (fun _ => β) :=
  if h : 0 < m.buckets.size then
    let ⟨replaced, ⟨r, _⟩⟩ := Raw₀.Const.getThenInsertIfNew? ⟨m, h⟩ a b
    ⟨replaced, r⟩
  else (none, m) -- will never happen for well-formed inputs

end

/--
Checks if a mapping for the given key exists and returns the key if it does, otherwise `none`.
The result in the `some` case is guaranteed to be pointer equal to the key in the map.
-/
@[inline] def getKey? [BEq α] [Hashable α] (m : Raw α β) (a : α) : Option α :=
  if h : 0 < m.buckets.size then
    Raw₀.getKey? ⟨m, h⟩ a
  else none -- will never happen for well-formed inputs

/--
Retrieves the key from the mapping that matches `a`. Ensures that such a mapping exists by
requiring a proof of `a ∈ m`. The result is guaranteed to be pointer equal to the key in the map.
-/
@[inline] def getKey [BEq α] [Hashable α] (m : Raw α β) (a : α) (h : a ∈ m) : α :=
  Raw₀.getKey ⟨m, by change dite .. = true at h; split at h <;> simp_all⟩ a
    (by change dite .. = true at h; split at h <;> simp_all)

/--
Checks if a mapping for the given key exists and returns the key if it does, otherwise `fallback`.
If a mapping exists the result is guaranteed to be pointer equal to the key in the map.
-/
@[inline] def getKeyD [BEq α] [Hashable α] (m : Raw α β) (a : α) (fallback : α) : α :=
  if h : 0 < m.buckets.size then
    Raw₀.getKeyD ⟨m, h⟩ a fallback
  else fallback -- will never happen for well-formed inputs

/--
Checks if a mapping for the given key exists and returns the key if it does, otherwise panics.
If no panic occurs the result is guaranteed to be pointer equal to the key in the map.
-/
@[inline] def getKey! [BEq α] [Hashable α] [Inhabited α] (m : Raw α β) (a : α) : α :=
  if h : 0 < m.buckets.size then
    Raw₀.getKey! ⟨m, h⟩ a
  else default -- will never happen for well-formed inputs

/--
Returns `true` if the hash map contains no mappings.

Note that if your `BEq` instance is not reflexive or your `Hashable` instance is not
lawful, then it is possible that this function returns `false` even though is not possible
to get anything out of the hash map.
-/
@[inline] def isEmpty (m : Raw α β) : Bool :=
  m.size == 0

/--
Modifies in place the value associated with a given key.

This function ensures that the value is used linearly.
-/
@[inline] def modify [BEq α] [LawfulBEq α] [Hashable α] (m : Raw α β) (a : α) (f : β a → β a) :
    Raw α β :=
  if h : 0 < m.buckets.size then
    Raw₀.modify ⟨m, h⟩ a f
  else
    ∅

@[inline, inherit_doc Raw.modify] def Const.modify [BEq α] [EquivBEq α] [Hashable α] {β : Type v}
    (m : Raw α (fun _ => β)) (a : α) (f : β → β) : Raw α (fun _ => β) :=
  if h : 0 < m.buckets.size then
    Raw₀.Const.modify ⟨m, h⟩ a f
  else
    ∅

/--
Modifies in place the value associated with a given key,
allowing creating new values and deleting values via an `Option` valued replacement function.

This function ensures that the value is used linearly.
-/
@[inline] def alter [BEq α] [LawfulBEq α] [Hashable α] (m : Raw α β)
    (a : α) (f : Option (β a) → Option (β a)) : Raw α β :=
  if h : 0 < m.buckets.size then
    Raw₀.alter ⟨m, h⟩ a f
  else
    ∅

@[inline, inherit_doc Raw.alter] def Const.alter [BEq α] [EquivBEq α] [Hashable α] {β : Type v}
    (m : Raw α (fun _ => β)) (a : α) (f : Option β → Option β) : Raw α (fun _ => β) :=
  if h : 0 < m.buckets.size then
    Raw₀.Const.alter ⟨m, h⟩ a f
  else
    ∅

/--
Monadically computes a value by folding the given function over the mappings in the hash
map in some order.
-/
@[inline] def foldM (f : δ → (a : α) → β a → m δ) (init : δ) (b : Raw α β) : m δ :=
  b.buckets.foldlM (fun acc l => l.foldlM f acc) init

/-- Folds the given function over the mappings in the hash map in some order. -/
@[inline] def fold (f : δ → (a : α) → β a → δ) (init : δ) (b : Raw α β) : δ :=
  Id.run (b.foldM (pure <| f · · ·) init)

/--
Monadically computes a value by folding the given function over the mappings in the hash
map in the reverse order used by `foldM`.
-/
@[inline] def foldRevM (f : δ → (a : α) → β a → m δ) (init : δ) (b : Raw α β) : m δ :=
  b.buckets.foldrM (fun l acc => l.foldrM (fun a b d => f d a b) acc) init

/--
Folds the given function over the mappings in the hash map in the reverse order used
by `foldM`. -/
@[inline] def foldRev (f : δ → (a : α) → β a → δ) (init : δ) (b : Raw α β) : δ :=
  Id.run (b.foldRevM (pure <| f · · ·) init)

/-- Carries out a monadic action on each mapping in the hash map in some order. -/
@[inline] def forM (f : (a : α) → β a → m PUnit) (b : Raw α β) : m PUnit :=
  b.buckets.forM (AssocList.forM f)

/-- Support for the `for` loop construct in `do` blocks. -/
@[inline] def forIn (f : (a : α) → β a → δ → m (ForInStep δ)) (init : δ) (b : Raw α β) : m δ :=
  ForIn.forIn b.buckets init (fun bucket acc => bucket.forInStep acc f)

instance : ForM m (Raw α β) ((a : α) × β a) where
  forM m f := m.forM (fun a b => f ⟨a, b⟩)

instance : ForIn m (Raw α β) ((a : α) × β a) where
  forIn m init f := m.forIn (fun a b acc => f ⟨a, b⟩ acc) init

namespace Const

variable {β : Type v}

/-!
We do not define `ForM` and `ForIn` instances that are specialized to constant `β`. Instead, we
define uncurried versions of `forM` and `forIn` that will be used in the `Const` lemmas and to
define the `ForM` and `ForIn` instances for `HashMap.Raw`.
-/

@[inline, inherit_doc forM] def forMUncurried (f : α × β → m PUnit)
    (b : Raw α (fun _ => β)) : m PUnit :=
  b.forM fun a b => f ⟨a, b⟩

@[inline, inherit_doc forIn] def forInUncurried
    (f : α × β → δ → m (ForInStep δ)) (init : δ) (b : Raw α (fun _ => β)) : m δ :=
  b.forIn (init := init) fun a b d => f ⟨a, b⟩ d

end Const

section Unverified

/-! We currently do not provide lemmas for the functions below. -/

/--
Updates the values of the hash map by applying the given function to all mappings, keeping
only those mappings where the function returns `some` value.
-/
@[inline] def filterMap {γ : α → Type w} (f : (a : α) → β a → Option (γ a)) (m : Raw α β) :
    Raw α γ :=
  if h : 0 < m.buckets.size then
    Raw₀.filterMap f ⟨m, h⟩
  else ∅ -- will never happen for well-formed inputs

/-- Updates the values of the hash map by applying the given function to all mappings. -/
@[inline] def map {γ : α → Type w} (f : (a : α) → β a → γ a) (m : Raw α β) : Raw α γ :=
  if h : 0 < m.buckets.size then
    Raw₀.map f ⟨m, h⟩
  else ∅ -- will never happen for well-formed inputs

/-- Removes all mappings of the hash map for which the given function returns `false`. -/
@[inline] def filter (f : (a : α) → β a → Bool) (m : Raw α β) : Raw α β :=
  if h : 0 < m.buckets.size then
    Raw₀.filter f ⟨m, h⟩
  else ∅ -- will never happen for well-formed inputs

/-- Transforms the hash map into an array of mappings in some order. -/
@[inline] def toArray (m : Raw α β) : Array ((a : α) × β a) :=
  m.fold (fun acc k v => acc.push ⟨k, v⟩) #[]

@[inline, inherit_doc Raw.toArray] def Const.toArray {β : Type v} (m : Raw α (fun _ => β)) :
    Array (α × β) :=
  m.fold (fun acc k v => acc.push ⟨k, v⟩) #[]

/-- Returns an array of all keys present in the hash map in some order. -/
@[inline] def keysArray (m : Raw α β) : Array α :=
  m.fold (fun acc k _ => acc.push k) #[]

/-- Returns a list of all values present in the hash map in some order. -/
@[inline] def values {β : Type v} (m : Raw α (fun _ => β)) : List β :=
  m.foldRev (fun acc _ v => v :: acc) []

/-- Returns an array of all values present in the hash map in some order. -/
@[inline] def valuesArray {β : Type v} (m : Raw α (fun _ => β)) : Array β :=
  m.fold (fun acc _ v => acc.push v) #[]

/--
Inserts multiple mappings into the hash map by iterating over the given collection and calling
`insert`. If the same key appears multiple times, the last occurrence takes precedence.

Note: this precedence behavior is true for `HashMap`, `DHashMap`, `HashMap.Raw` and `DHashMap.Raw`.
The `insertMany` function on `HashSet` and `HashSet.Raw` behaves differently: it will prefer the first
appearance.
-/
@[inline] def insertMany [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ ((a : α) × β a)]
    (m : Raw α β) (l : ρ) : Raw α β :=
  if h : 0 < m.buckets.size then
    (Raw₀.insertMany ⟨m, h⟩ l).1
  else m -- will never happen for well-formed inputs

@[inline, inherit_doc Raw.insertMany] def Const.insertMany {β : Type v} [BEq α] [Hashable α]
    {ρ : Type w} [ForIn Id ρ (α × β)] (m : Raw α (fun _ => β)) (l : ρ) : Raw α (fun _ => β) :=
  if h : 0 < m.buckets.size then
    (Raw₀.Const.insertMany ⟨m, h⟩ l).1
  else m -- will never happen for well-formed inputs

/--
Inserts multiple keys with the value `()` into the hash map by iterating over the given collection
and calling `insertIfNew`. If the same key appears multiple times, the first occurrence takes
precedence.

This is mainly useful to implement `HashSet.insertMany`, so if you are considering using this,
`HashSet` or `HashSet.Raw` might be a better fit for you.
-/
@[inline] def Const.insertManyIfNewUnit [BEq α] [Hashable α] {ρ : Type w}
    [ForIn Id ρ α] (m : Raw α (fun _ => Unit)) (l : ρ) : Raw α (fun _ => Unit) :=
  if h : 0 < m.buckets.size then
    (Raw₀.Const.insertManyIfNewUnit ⟨m, h⟩ l).1
  else m -- will never happen for well-formed inputs

/-- Computes the union of the given hash maps, by traversing `m₂` and inserting its elements into `m₁`. -/
@[inline] def union [BEq α] [Hashable α] (m₁ m₂ : Raw α β) : Raw α β :=
  m₂.fold (init := m₁) fun acc x => acc.insert x

instance [BEq α] [Hashable α] : Union (Raw α β) := ⟨union⟩

/-- Creates a hash map from an array of keys, associating the value `()` with each key.

This is mainly useful to implement `HashSet.ofArray`, so if you are considering using this,
`HashSet` or `HashSet.Raw` might be a better fit for you. -/
@[inline] def Const.unitOfArray [BEq α] [Hashable α] (l : Array α) :
    Raw α (fun _ => Unit) :=
  Const.insertManyIfNewUnit ∅ l

/--
Returns the number of buckets in the internal representation of the hash map. This function may be
useful for things like monitoring system health, but it should be considered an internal
implementation detail.
-/
def Internal.numBuckets (m : Raw α β) : Nat :=
  m.buckets.size

end Unverified

/-- Transforms the hash map into a list of mappings in some order. -/
@[inline] def toList (m : Raw α β) : List ((a : α) × β a) :=
  m.foldRev (fun acc k v => ⟨k, v⟩ :: acc) []

@[inline, inherit_doc Raw.toList] def Const.toList {β : Type v} (m : Raw α (fun _ => β)) :
    List (α × β) :=
  m.foldRev (fun acc k v => ⟨k, v⟩ :: acc) []

instance [Repr α] [(a : α) → Repr (β a)] : Repr (Raw α β) where
  reprPrec m prec := Repr.addAppParen ("Std.DHashMap.Raw.ofList " ++ reprArg m.toList) prec

/-- Returns a list of all keys present in the hash map in some order. -/
@[inline] def keys (m : Raw α β) : List α :=
  m.foldRev (fun acc k _ => k :: acc) []

/-- Creates a hash map from a list of mappings. If the same key appears multiple times, the last
occurrence takes precedence. -/
@[inline] def ofList [BEq α] [Hashable α] (l : List ((a : α) × β a)) : Raw α β :=
  insertMany ∅ l

@[inline, inherit_doc Raw.ofList] def Const.ofList {β : Type v} [BEq α] [Hashable α]
    (l : List (α × β)) : Raw α (fun _ => β) :=
  Const.insertMany ∅ l

/-- Creates a hash map from a list of keys, associating the value `()` with each key.

This is mainly useful to implement `HashSet.ofList`, so if you are considering using this,
`HashSet` or `HashSet.Raw` might be a better fit for you. -/
@[inline] def Const.unitOfList [BEq α] [Hashable α] (l : List α) :
    Raw α (fun _ => Unit) :=
  Const.insertManyIfNewUnit ∅ l

section WF

/--
Well-formedness predicate for hash maps. Users of `DHashMap` will not need to interact with
this. Users of `DHashMap.Raw` will need to provide proofs of `WF` to lemmas and should use lemmas
like `WF.empty` and `WF.insert` (which are always named exactly like the operations they are about)
to show that map operations preserve well-formedness. The constructors of this type are internal
implementation details and should not be accessed by users.
-/
inductive WF : {α : Type u} → {β : α → Type v} → [BEq α] → [Hashable α] → Raw α β → Prop where
  -- Implementation note: the reason why we provide the `[EquivBEq α] [LawfulHashable α]` is so that
  -- we can write down `DHashMap.map` and `DHashMap.filterMap` in `AdditionalOperations.lean`
  -- without requiring these proofs just to invoke the operations.
  /-- Internal implementation detail of the hash map -/
  | wf {α β} [BEq α] [Hashable α] {m : Raw α β} : 0 < m.buckets.size →
      (∀ [EquivBEq α] [LawfulHashable α], Raw.WFImp m) → WF m
  /-- Internal implementation detail of the hash map -/
  | empty₀ {α β} [BEq α] [Hashable α] {c} : WF (Raw₀.empty c : Raw₀ α β).1
  /-- Internal implementation detail of the hash map -/
  | insert₀ {α β} [BEq α] [Hashable α] {m : Raw α β} {h a b} : WF m → WF (Raw₀.insert ⟨m, h⟩ a b).1
  /-- Internal implementation detail of the hash map -/
  | containsThenInsert₀ {α β} [BEq α] [Hashable α] {m : Raw α β} {h a b} :
      WF m → WF (Raw₀.containsThenInsert ⟨m, h⟩ a b).2.1
  /-- Internal implementation detail of the hash map -/
  | containsThenInsertIfNew₀ {α β} [BEq α] [Hashable α] {m : Raw α β} {h a b} :
      WF m → WF (Raw₀.containsThenInsertIfNew ⟨m, h⟩ a b).2.1
  /-- Internal implementation detail of the hash map -/
  | erase₀ {α β} [BEq α] [Hashable α] {m : Raw α β} {h a} : WF m → WF (Raw₀.erase ⟨m, h⟩ a).1
  /-- Internal implementation detail of the hash map -/
  | insertIfNew₀ {α β} [BEq α] [Hashable α] {m : Raw α β} {h a b} :
      WF m → WF (Raw₀.insertIfNew ⟨m, h⟩ a b).1
  /-- Internal implementation detail of the hash map -/
  | getThenInsertIfNew?₀ {α β} [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} {h a b} :
      WF m → WF (Raw₀.getThenInsertIfNew? ⟨m, h⟩ a b).2.1
  /-- Internal implementation detail of the hash map -/
  | filter₀ {α β} [BEq α] [Hashable α] {m : Raw α β} {h f} : WF m → WF (Raw₀.filter f ⟨m, h⟩).1
  /-- Internal implementation detail of the hash map -/
  | constGetThenInsertIfNew?₀ {α β} [BEq α] [Hashable α] {m : Raw α (fun _ => β)} {h a b} :
      WF m → WF (Raw₀.Const.getThenInsertIfNew? ⟨m, h⟩ a b).2.1
  /-- Internal implementation detail of the hash map -/
  | modify₀ {α β} [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} {h a} {f : β a → β a} :
      WF m → WF (Raw₀.modify ⟨m, h⟩ a f).1
  /-- Internal implementation detail of the hash map -/
  | constModify₀ {α} {β : Type v} [BEq α] [Hashable α] {m : Raw α (fun _ => β)} {h a} {f : β → β} :
      WF m → WF (Raw₀.Const.modify ⟨m, h⟩ a f).1
  /-- Internal implementation detail of the hash map -/
  | alter₀ {α β} [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} {h a}
      {f : Option (β a) → Option (β a)} : WF m → WF (Raw₀.alter ⟨m, h⟩ a f).1
  /-- Internal implementation detail of the hash map -/
  | constAlter₀ {α} {β : Type v} [BEq α] [Hashable α] {m : Raw α (fun _ => β)} {h a}
      {f : Option β → Option β} : WF m → WF (Raw₀.Const.alter ⟨m, h⟩ a f).1

/-- Internal implementation detail of the hash map -/
theorem WF.size_buckets_pos [BEq α] [Hashable α] (m : Raw α β) : WF m → 0 < m.buckets.size
  | wf h₁ _ => h₁
  | empty₀ => (Raw₀.empty _).2
  | insert₀ _ => (Raw₀.insert ⟨_, _⟩ _ _).2
  | containsThenInsert₀ _ => (Raw₀.containsThenInsert ⟨_, _⟩ _ _).2.2
  | containsThenInsertIfNew₀ _ => (Raw₀.containsThenInsertIfNew ⟨_, _⟩ _ _).2.2
  | erase₀ _ => (Raw₀.erase ⟨_, _⟩ _).2
  | insertIfNew₀ _ => (Raw₀.insertIfNew ⟨_, _⟩ _ _).2
  | getThenInsertIfNew?₀ _ => (Raw₀.getThenInsertIfNew? ⟨_, _⟩ _ _).2.2
  | filter₀ _ => (Raw₀.filter _ ⟨_, _⟩).2
  | constGetThenInsertIfNew?₀ _ => (Raw₀.Const.getThenInsertIfNew? ⟨_, _⟩ _ _).2.2
  | modify₀ _ => (Raw₀.modify _ _ _).2
  | constModify₀ _ => (Raw₀.Const.modify _ _ _).2
  | alter₀ _ => (Raw₀.alter _ _ _).2
  | constAlter₀ _ => (Raw₀.Const.alter _ _ _).2

@[simp] theorem WF.empty [BEq α] [Hashable α] {c : Nat} : (Raw.empty c : Raw α β).WF :=
  .empty₀

@[simp] theorem WF.emptyc [BEq α] [Hashable α] : (∅ : Raw α β).WF :=
  .empty

theorem WF.insert [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β a} (h : m.WF) :
    (m.insert a b).WF := by
  simpa [Raw.insert, h.size_buckets_pos] using .insert₀ h

theorem WF.containsThenInsert [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β a} (h : m.WF) :
    (m.containsThenInsert a b).2.WF := by
  simpa [Raw.containsThenInsert, h.size_buckets_pos] using .containsThenInsert₀ h

theorem WF.containsThenInsertIfNew [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β a} (h : m.WF) :
    (m.containsThenInsertIfNew a b).2.WF := by
  simpa [Raw.containsThenInsertIfNew, h.size_buckets_pos] using .containsThenInsertIfNew₀ h

theorem WF.erase [BEq α] [Hashable α] {m : Raw α β} {a : α} (h : m.WF) : (m.erase a).WF := by
  simpa [Raw.erase, h.size_buckets_pos] using .erase₀ h

theorem WF.insertIfNew [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β a} (h : m.WF) :
    (m.insertIfNew a b).WF := by
  simpa [Raw.insertIfNew, h.size_buckets_pos] using .insertIfNew₀ h

theorem WF.getThenInsertIfNew? [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} {a : α} {b : β a}
    (h : m.WF) : (m.getThenInsertIfNew? a b).2.WF := by
  simpa [Raw.getThenInsertIfNew?, h.size_buckets_pos] using .getThenInsertIfNew?₀ h

theorem WF.filter [BEq α] [Hashable α] {m : Raw α β} {f : (a : α) → β a → Bool} (h : m.WF) :
    (m.filter f).WF := by
  simpa [Raw.filter, h.size_buckets_pos] using .filter₀ h

theorem WF.Const.getThenInsertIfNew? {β : Type v} [BEq α] [Hashable α] {m : Raw α (fun _ => β)}
    {a : α} {b : β} (h : m.WF) : (Const.getThenInsertIfNew? m a b).2.WF := by
  simpa [Raw.Const.getThenInsertIfNew?, h.size_buckets_pos] using .constGetThenInsertIfNew?₀ h

theorem WF.insertMany [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] {m : Raw α β}
    {l : ρ} (h : m.WF) : (m.insertMany l).WF := by
  simpa [Raw.insertMany, h.size_buckets_pos] using
    (Raw₀.insertMany ⟨m, h.size_buckets_pos⟩ l).2 _ WF.insert₀ h

theorem WF.Const.insertMany {β : Type v} [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ (α × β)]
    {m : Raw α (fun _ => β)} {l : ρ} (h : m.WF) : (Const.insertMany m l).WF := by
  simpa [Raw.Const.insertMany, h.size_buckets_pos] using
    (Raw₀.Const.insertMany ⟨m, h.size_buckets_pos⟩ l).2 _ WF.insert₀ h

theorem WF.Const.insertManyIfNewUnit [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ α]
    {m : Raw α (fun _ => Unit)} {l : ρ} (h : m.WF) : (Const.insertManyIfNewUnit m l).WF := by
  simpa [Raw.Const.insertManyIfNewUnit, h.size_buckets_pos] using
    (Raw₀.Const.insertManyIfNewUnit ⟨m, h.size_buckets_pos⟩ l).2 _ WF.insertIfNew₀ h

theorem WF.ofList [BEq α] [Hashable α] {l : List ((a : α) × β a)} :
    (ofList l : Raw α β).WF :=
  .insertMany WF.empty

theorem WF.Const.ofList {β : Type v} [BEq α] [Hashable α] {l : List (α × β)} :
    (Const.ofList l : Raw α (fun _ => β)).WF :=
  Const.insertMany WF.empty

theorem WF.Const.unitOfList [BEq α] [Hashable α] {l : List α} :
    (Const.unitOfList l : Raw α (fun _ => Unit)).WF :=
  Const.insertManyIfNewUnit WF.empty

end WF

end Raw

end DHashMap

end Std
