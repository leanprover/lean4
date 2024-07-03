/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
prelude
import Std.Classes.BEq
import Std.Classes.LawfulHashable
import Std.Data.DHashMap.Internal.Defs

/-!
# Dependent hash maps

This file develops the two types `Std.Data.DHashMap.Raw` and `Std.Data.DHashMap` of dependent hash
maps. The difference between these types is that the former does not bundle the well-formedness
invariant and is thus safe to use in nested inductive types. The well-formedness predicate is
available as `Std.Data.DHashMap.Raw.WF` and this file proves that all operations preserve
well-formedness. When in doubt, prefer `DHashMap` over `DHashMap.Raw`.

The operations `map` and `filterMap` on `Std.Data.DHashMap` are defined in the module
`Std.Data.DHashMap.AdditionalOperations`.

Lemmas about the operations on `Std.Data.DHashMap` and `Std.Data.DHashMap.Raw` are available in the
modules `Std.Data.DHashMap.Lemmas` and `Std.Data.DHashMap.RawLemmas`.

For implementation notes, see the docstring of the module `Std.Data.DHashMap.Internal.Defs`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w

variable {α : Type u} {β : α → Type v} {δ : Type w} {m : Type w → Type w} [Monad m]

namespace Std

open DHashMap.Internal DHashMap.Internal.List

namespace DHashMap

namespace Raw

/-- Creates a new empty hash map. The optional parameter `capacity` can be supplied to presize the
map so that it can hold the given number of mappings without reallocating. It is also possible to
use the empty collection notations `∅` and `{}` to create an empty hash map with the default
capacity. -/
@[inline] def empty (capacity := 8) : Raw α β :=
  (Raw₀.empty capacity).1

instance : EmptyCollection (Raw α β) where
  emptyCollection := empty

/-- Insert the given mapping into the map, replacing an existing mapping for the key if there is
one. -/
@[inline] def insert [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β a) : Raw α β :=
  if h : 0 < m.buckets.size then
    (Raw₀.insert ⟨m, h⟩ a b).1
  else m -- will never happen for well-formed inputs

/-- If there is no mapping for the given key, insert the given mapping into the map. Otherwise,
return the map unaltered. -/
@[inline] def insertIfNew [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β a) : Raw α β :=
  if h : 0 < m.buckets.size then
    (Raw₀.insertIfNew ⟨m, h⟩ a b).1
  else m -- will never happen for well-formed inputs

/-- Equivalent to (but potentially faster than) calling `contains` followed by `insert`. -/
@[inline] def containsThenInsert [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β a) : Bool × Raw α β:=
  if h : 0 < m.buckets.size then
    let ⟨replaced, ⟨r, _⟩⟩ := Raw₀.containsThenInsert ⟨m, h⟩ a b
    ⟨replaced, r⟩
  else (false, m) -- will never happen for well-formed inputs

/-- Equivalent to (but potentially faster than) calling `get?` followed by `insertIfNew`. -/
@[inline] def getThenInsertIfNew? [BEq α] [Hashable α] [LawfulBEq α] (m : Raw α β) (a : α) (b : β a) : Option (β a) × Raw α β :=
  if h : 0 < m.buckets.size then
    let ⟨previous, ⟨r, _⟩⟩ := Raw₀.getThenInsertIfNew? ⟨m, h⟩ a b
    ⟨previous, r⟩
  else (none, m) -- will never happen for well-formed inputs

/-- Tries to retrieve the mapping for the given key, returning `none` if no such mapping is present.

Uses the `LawfulBEq` instance to cast the retrieved value to the correct type. -/
@[inline] def get? [BEq α] [LawfulBEq α] [Hashable α] (m : Raw α β) (a : α) : Option (β a) :=
  if h : 0 < m.buckets.size then
    Raw₀.get? ⟨m, h⟩ a
  else none -- will never happen for well-formed inputs

/-- Returns `true` if there is a mapping for the given key. There is also a `Prop`-valued version
of this: `a ∈ m` is equivalent to `m.contains a = true`.

Observe that this is different behavior than for lists: for lists, `∈` uses `=` and `contains` use
`==` for comparisons, while for hash maps, both use `==`. -/
@[inline] def contains [BEq α] [Hashable α] (m : Raw α β) (a : α) : Bool :=
  if h : 0 < m.buckets.size then
    Raw₀.contains ⟨m, h⟩ a
  else false -- will never happen for well-formed inputs

instance [BEq α] [Hashable α] : Membership α (Raw α β) where
  mem a m := m.contains a

instance [BEq α] [Hashable α] {m : Raw α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (m.contains a))

/-- Retrieves the mapping for the given key. Ensures that such a mapping exists by requiring a proof
of `a ∈ m`.

Uses the `LawfulBEq` instance to cast the retrieved value to the correct type. -/
@[inline] def get [BEq α] [Hashable α] [LawfulBEq α] (m : Raw α β) (a : α) (h : a ∈ m) : β a :=
  Raw₀.get ⟨m, by change dite .. = true at h; split at h <;> simp_all⟩ a
    (by change dite .. = true at h; split at h <;> simp_all)

/-- Tries to retrieve the mapping for the given key, returning `fallback` if no such mapping is
present.

Uses the `LawfulBEq` instance to cast the retrieved value to the correct type. -/
@[inline] def getD [BEq α] [Hashable α] [LawfulBEq α] (m : Raw α β) (a : α) (fallback : β a) : β a :=
  if h : 0 < m.buckets.size then
    Raw₀.getD ⟨m, h⟩ a fallback
  else fallback -- will never happen for well-formed inputs

/-- Tries to retrieve the mapping for the given key, panicking if no such mapping is present.

Uses the `LawfulBEq` instance to cast the retrieved value to the correct type. -/
@[inline] def get! [BEq α] [Hashable α] [LawfulBEq α] (m : Raw α β) (a : α) [Inhabited (β a)] : β a :=
  if h : 0 < m.buckets.size then
    Raw₀.get! ⟨m, h⟩ a
  else default -- will never happen for well-formed inputs

/-- Removes the mapping for the given key if it exists.

Uses the `LawfulBEq` instance to cast the retrieved value to the correct type. -/
@[inline] def remove [BEq α] [Hashable α] (m : Raw α β) (a : α) : Raw α β :=
  if h : 0 < m.buckets.size then
    Raw₀.remove ⟨m, h⟩ a
  else m -- will never happen for well-formed inputs

section

variable {β : Type v}

/-- Tries to retrieve the mapping for the given key, returning `none` if no such mapping is present.
-/
@[inline] def Const.get? [BEq α] [Hashable α] (m : Raw α (fun _ => β)) (a : α) : Option β :=
  if h : 0 < m.buckets.size then
    Raw₀.Const.get? ⟨m, h⟩ a
  else none -- will never happen for well-formed inputs

/-- Retrieves the mapping for the given key. Ensures that such a mapping exists by requiring a proof
of `a ∈ m`. -/
@[inline] def Const.get [BEq α] [Hashable α] (m : Raw α (fun _ => β)) (a : α) (h : a ∈ m) : β :=
  Raw₀.Const.get ⟨m, by change dite .. = true at h; split at h <;> simp_all⟩ a
    (by change dite .. = true at h; split at h <;> simp_all)

/-- Tries to retrieve the mapping for the given key, returning `fallback` if no such mapping is
present. -/
@[inline] def Const.getD [BEq α] [Hashable α] (m : Raw α (fun _ => β)) (a : α) (fallback : β) : β :=
  if h : 0 < m.buckets.size then
    Raw₀.Const.getD ⟨m, h⟩ a fallback
  else fallback -- will never happen for well-formed inputs

/-- Tries to retrieve the mapping for the given key, panicking if no such mapping is present. -/
@[inline] def Const.get! [BEq α] [Hashable α] [Inhabited β] (m : Raw α (fun _ => β)) (a : α) : β :=
  if h : 0 < m.buckets.size then
    Raw₀.Const.get! ⟨m, h⟩ a
  else default -- will never happen for well-formed inputs

/-- Equivalent to (but potentially faster than) calling `Const.get?` followed by `insertIfNew`. -/
@[inline] def Const.getThenInsertIfNew? [BEq α] [Hashable α] (m : Raw α (fun _ => β)) (a : α) (b : β) :
    Option β × Raw α (fun _ => β) :=
  if h : 0 < m.buckets.size then
    let ⟨replaced, ⟨r, _⟩⟩ := Raw₀.Const.getThenInsertIfNew? ⟨m, h⟩ a b
    ⟨replaced, r⟩
  else (none, m) -- will never happen for well-formed inputs

end

/-- Returns `true` if the hash map contains no mappings.

Note that if your `BEq` instance is not reflexive or your `Hashable` instance is not
lawful, then it is possible that this function returns `false` even though is not possible
to get anything out of the hash map. -/
@[inline] def isEmpty (m : Raw α β) : Bool :=
  m.size == 0

section Unverified

/-! We currently do not provide lemmas for the functions below. -/

/-- Updates the values of the hash map by applying the given function to all mappings, keeping
only those mappings where the function returns `some` value. -/
@[inline] def filterMap {γ : α → Type w} (f : (a : α) → β a → Option (γ a)) (m : Raw α β) : Raw α γ :=
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

/-- Folds the given function over the mappings in the hash map in some order. -/
@[inline] def foldlM (f : δ → (a : α) → β a → m δ) (init : δ) (b : Raw α β) : m δ :=
  b.buckets.foldlM (fun acc l => l.foldlM f acc) init

/-- Folds the given function over the mappings in the hash map in some order. -/
@[inline] def foldl (f : δ → (a : α) → β a → δ) (init : δ) (b : Raw α β) : δ :=
  Id.run (b.foldlM f init)

/-- Folds the given function over the mappings in the hash map in some order. -/
@[inline] def forM (f : (a : α) → β a → m PUnit) (b : Raw α β) : m PUnit :=
  b.buckets.forM (AssocList.forM f)

/-- Support for the `for` loop construct in `do` blocks. -/
@[inline] def forIn (f : (a : α) → β a → δ → m (ForInStep δ)) (init : δ) (b : Raw α β) : m δ :=
  b.buckets.forIn init (fun bucket acc => bucket.forInStep acc f)

instance : ForM m (Raw α β) (Σ a, β a) where
  forM m f := m.forM (fun a b => f ⟨a, b⟩)

instance : ForIn m (Raw α β) (Σ a, β a) where
  forIn m init f := m.forIn (fun a b acc => f ⟨a, b⟩ acc) init

/-- Transforms the hash map into a list of mappings in some order. -/
@[inline] def toList (m : Raw α β) : List (Σ a, β a) :=
  m.foldl (fun acc k v => ⟨k, v⟩ :: acc) []

/-- Transforms the hash map into an array of mappings in some order. -/
@[inline] def toArray (m : Raw α β) : Array (Σ a, β a) :=
  m.foldl (fun acc k v => acc.push ⟨k, v⟩) #[]

@[inline, inherit_doc Raw.toList] def Const.toList {β : Type v} (m : Raw α (fun _ => β)) : List (α × β) :=
  m.foldl (fun acc k v => ⟨k, v⟩ :: acc) []

@[inline, inherit_doc Raw.toArray] def Const.toArray {β : Type v} (m : Raw α (fun _ => β)) : Array (α × β) :=
  m.foldl (fun acc k v => acc.push ⟨k, v⟩) #[]

/-- Returns a list of all keys present in the hash map in some order. -/
@[inline] def keys (m : Raw α β) : List α :=
  m.foldl (fun acc k _ => k :: acc) []

/-- Returns an array of all keys present in the hash map in some order. -/
@[inline] def keysArray (m : Raw α β) : Array α :=
  m.foldl (fun acc k _ => acc.push k) #[]

/-- Returns a list of all values present in the hash map in some order. -/
@[inline] def values {β : Type v} (m : Raw α (fun _ => β)) : List β :=
  m.foldl (fun acc _ v => v :: acc) []

/-- Inserts multiple mappings into the hash map by iterating over the given collection and calling
`insert`. If the same key appears multiple times, the last occurrence takes precendence. -/
@[inline] def insertMany [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] (m : Raw α β) (l : ρ) : Raw α β :=
  if h : 0 < m.buckets.size then
    (Raw₀.insertMany ⟨m, h⟩ l).1
  else m -- will never happen for well-formed inputs

@[inline, inherit_doc Raw.insertMany] def Const.insertMany {β : Type v} [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ (α × β)] (m : Raw α (fun _ => β)) (l : ρ) : Raw α (fun _ => β) :=
  if h : 0 < m.buckets.size then
    (Raw₀.Const.insertMany ⟨m, h⟩ l).1
  else m -- will never happen for well-formed inputs

@[inline, inherit_doc Raw.insertMany] def Const.insertManyUnit [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ α] (m : Raw α (fun _ => Unit)) (l : ρ) : Raw α (fun _ => Unit) :=
  if h : 0 < m.buckets.size then
    (Raw₀.Const.insertManyUnit ⟨m, h⟩ l).1
  else m -- will never happen for well-formed inputs

/-- Creates a hash map from a list of mappings. -/
@[inline] def ofList [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] (l : ρ) : Raw α β :=
  insertMany ∅ l

@[inline, inherit_doc Raw.ofList] def Const.ofList {β : Type v} [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ (α × β)] (l : ρ) : Raw α (fun _ => β) :=
  Const.insertMany ∅ l

@[inline, inherit_doc Raw.ofList] def Const.unitOfList [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ α] (l : ρ) : Raw α (fun _ => Unit) :=
  Const.insertManyUnit ∅ l

/-- Returns the number of buckets in the internal representation of the hash map. This function may
be useful for things like monitoring system health, but it should be considered an internal
implementation detail. -/
def Internal.numBuckets (m : Raw α β) : Nat :=
  m.buckets.size

instance [Repr α] [(a : α) → Repr (β a)] : Repr (Raw α β) where
  reprPrec m prec := Repr.addAppParen ("Std.DHashMap.Raw.ofList " ++ reprArg m.toList) prec

end Unverified

section WF

/--
Well-formedness predicate for hash maps. Users of `DHashMap` will not need to interact with this.
Users of `DHashMap.Raw` will need to provide proofs of `WF` to lemmas and should use the lemmas
`WF.empty`, `WF.emptyc`, `WF.insert`, `WF.containsThenInsert`, `WF.remove`, `WF.insertIfNew`,
`WF.getThenInsertIfNew?`, `WF.filter`, `WF.Const.getThenInsertIfNew?`, `WF.filterMap` and `WF.map`
to show that map operations preserve well-formedness. The constructors of this type are internal
implementation details and should not be accessed by users.
-/
inductive WF : {α : Type u} → {β : α → Type v} → [BEq α] → [Hashable α] → Raw α β → Prop where
  -- Implementation note: the reason why we provide the `[EquivBEq α] [LawfulHashable α]` is so that we can write down
  -- `DHashMap.map` and `DHashMap.filterMap` in `AdditionalOperations.lean` without requiring these proofs just to invoke
  -- the operations.
  /-- Internal implementation detail of the hash map -/
  | wf {α β} [BEq α] [Hashable α] {m : Raw α β} : 0 < m.buckets.size → (∀ [EquivBEq α] [LawfulHashable α], Raw.WFImp m) → WF m
  /-- Internal implementation detail of the hash map -/
  | empty₀ {α β} [BEq α] [Hashable α] {c} : WF (Raw₀.empty c : Raw₀ α β).1
  /-- Internal implementation detail of the hash map -/
  | insert₀ {α β} [BEq α] [Hashable α] {m : Raw α β} {h a b} : WF m → WF (Raw₀.insert ⟨m, h⟩ a b).1
  /-- Internal implementation detail of the hash map -/
  | containsThenInsert₀ {α β} [BEq α] [Hashable α] {m : Raw α β} {h a b} : WF m → WF (Raw₀.containsThenInsert ⟨m, h⟩ a b).2.1
  /-- Internal implementation detail of the hash map -/
  | remove₀ {α β} [BEq α] [Hashable α] {m : Raw α β} {h a} : WF m → WF (Raw₀.remove ⟨m, h⟩ a).1
  /-- Internal implementation detail of the hash map -/
  | insertIfNew₀ {α β} [BEq α] [Hashable α] {m : Raw α β} {h a b} : WF m → WF (Raw₀.insertIfNew ⟨m, h⟩ a b).1
  /-- Internal implementation detail of the hash map -/
  | getThenInsertIfNew?₀ {α β} [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} {h a b} : WF m → WF (Raw₀.getThenInsertIfNew? ⟨m, h⟩ a b).2.1
  /-- Internal implementation detail of the hash map -/
  | filter₀ {α β} [BEq α] [Hashable α] {m : Raw α β} {h f} : WF m → WF (Raw₀.filter f ⟨m, h⟩).1
  /-- Internal implementation detail of the hash map -/
  | constGetThenInsertIfNew?₀ {α β} [BEq α] [Hashable α] {m : Raw α (fun _ => β)} {h a b} : WF m → WF (Raw₀.Const.getThenInsertIfNew? ⟨m, h⟩ a b).2.1

theorem WF.size_buckets_pos [BEq α] [Hashable α] (m : Raw α β) : WF m → 0 < m.buckets.size
  | wf h₁ _ => h₁
  | empty₀ => (Raw₀.empty _).2
  | insert₀ _ => (Raw₀.insert ⟨_, _⟩ _ _).2
  | containsThenInsert₀ _ => (Raw₀.containsThenInsert ⟨_, _⟩ _ _).2.2
  | remove₀ _ => (Raw₀.remove ⟨_, _⟩ _).2
  | insertIfNew₀ _ => (Raw₀.insertIfNew ⟨_, _⟩ _ _).2
  | getThenInsertIfNew?₀ _ => (Raw₀.getThenInsertIfNew? ⟨_, _⟩ _ _).2.2
  | filter₀ _ => (Raw₀.filter _ ⟨_, _⟩).2
  | constGetThenInsertIfNew?₀ _ => (Raw₀.Const.getThenInsertIfNew? ⟨_, _⟩ _ _).2.2

@[simp] theorem WF.empty [BEq α] [Hashable α] {c : Nat} : (Raw.empty c : Raw α β).WF :=
  .empty₀

@[simp] theorem WF.emptyc [BEq α] [Hashable α] : (∅ : Raw α β).WF :=
  .empty

theorem WF.insert [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β a} (h : m.WF) : (m.insert a b).WF := by
  simpa [Raw.insert, h.size_buckets_pos] using .insert₀ h

theorem WF.containsThenInsert [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β a} (h : m.WF) : (m.containsThenInsert a b).2.WF := by
  simpa [Raw.containsThenInsert, h.size_buckets_pos] using .containsThenInsert₀ h

theorem WF.remove [BEq α] [Hashable α] {m : Raw α β} {a : α} (h : m.WF) : (m.remove a).WF := by
  simpa [Raw.remove, h.size_buckets_pos] using .remove₀ h

theorem WF.insertIfNew [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β a} (h : m.WF) : (m.insertIfNew a b).WF := by
  simpa [Raw.insertIfNew, h.size_buckets_pos] using .insertIfNew₀ h

theorem WF.getThenInsertIfNew? [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} {a : α} {b : β a} (h : m.WF) :
    (m.getThenInsertIfNew? a b).2.WF := by
  simpa [Raw.getThenInsertIfNew?, h.size_buckets_pos] using .getThenInsertIfNew?₀ h

theorem WF.filter [BEq α] [Hashable α] {m : Raw α β} {f : (a : α) → β a → Bool} (h : m.WF) :
    (m.filter f).WF := by
  simpa [Raw.filter, h.size_buckets_pos] using .filter₀ h

theorem WF.Const.getThenInsertIfNew? {β : Type v} [BEq α] [Hashable α] {m : Raw α (fun _ => β)} {a : α} {b : β} (h : m.WF) :
    (Const.getThenInsertIfNew? m a b).2.WF := by
  simpa [Raw.Const.getThenInsertIfNew?, h.size_buckets_pos] using .constGetThenInsertIfNew?₀ h

theorem WF.insertMany [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] {m : Raw α β} {l : ρ} (h : m.WF) :
    (m.insertMany l).WF := by
  simpa [Raw.insertMany, h.size_buckets_pos] using (Raw₀.insertMany ⟨m, h.size_buckets_pos⟩ l).2 _ WF.insert₀ h

theorem WF.Const.insertMany {β : Type v} [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ (α × β)] {m : Raw α (fun _ => β)} {l : ρ} (h : m.WF) :
    (Const.insertMany m l).WF := by
  simpa [Raw.Const.insertMany, h.size_buckets_pos] using (Raw₀.Const.insertMany ⟨m, h.size_buckets_pos⟩ l).2 _ WF.insert₀ h

theorem WF.Const.insertManyUnit [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ α] {m : Raw α (fun _ => Unit)} {l : ρ} (h : m.WF) :
    (Const.insertManyUnit m l).WF := by
  simpa [Raw.Const.insertManyUnit, h.size_buckets_pos] using (Raw₀.Const.insertManyUnit ⟨m, h.size_buckets_pos⟩ l).2 _ WF.insert₀ h

theorem WF.ofList [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] {l : ρ} : (ofList l : Raw α β).WF :=
  .insertMany WF.empty

theorem WF.Const.ofList {β : Type v} [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ (α × β)] {l : ρ} : (Const.ofList l : Raw α (fun _ => β)).WF :=
  Const.insertMany WF.empty

theorem WF.Const.unitOfList [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ α] {l : ρ} : (Const.unitOfList l : Raw α (fun _ => Unit)).WF :=
  Const.insertManyUnit WF.empty

end WF

end Raw

end DHashMap

/-- Dependent hash maps. -/
def DHashMap (α : Type u) (β : α → Type v) [BEq α] [Hashable α] := { m : DHashMap.Raw α β // m.WF }

namespace DHashMap

@[inline, inherit_doc Raw.empty] def empty [BEq α] [Hashable α] (capacity := 8) : DHashMap α β :=
  ⟨Raw.empty capacity, .empty₀⟩

instance [BEq α] [Hashable α] : EmptyCollection (DHashMap α β) where
  emptyCollection := empty

@[inline, inherit_doc Raw.insert] def insert [BEq α] [Hashable α] (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β :=
  ⟨Raw₀.insert ⟨m.1, m.2.size_buckets_pos⟩ a b, .insert₀ m.2⟩

@[inline, inherit_doc Raw.insertIfNew] def insertIfNew [BEq α] [Hashable α] (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β :=
  ⟨Raw₀.insertIfNew ⟨m.1, m.2.size_buckets_pos⟩ a b, .insertIfNew₀ m.2⟩

@[inline, inherit_doc Raw.containsThenInsert] def containsThenInsert [BEq α] [Hashable α] (m : DHashMap α β) (a : α) (b : β a) : Bool × DHashMap α β :=
  let m' := Raw₀.containsThenInsert ⟨m.1, m.2.size_buckets_pos⟩ a b
  ⟨m'.1, ⟨m'.2.1, .containsThenInsert₀ m.2⟩⟩

@[inline, inherit_doc Raw.getThenInsertIfNew?] def getThenInsertIfNew? [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap α β) (a : α) (b : β a) : Option (β a) × DHashMap α β :=
  let m' := Raw₀.getThenInsertIfNew? ⟨m.1, m.2.size_buckets_pos⟩ a b
  ⟨m'.1, ⟨m'.2.1, .getThenInsertIfNew?₀ m.2⟩⟩

@[inline, inherit_doc Raw.get?] def get? [BEq α] [LawfulBEq α] [Hashable α] (m : DHashMap α β) (a : α) : Option (β a) :=
  Raw₀.get? ⟨m.1, m.2.size_buckets_pos⟩ a

@[inline, inherit_doc Raw.contains] def contains [BEq α] [Hashable α] (m : DHashMap α β) (a : α) : Bool :=
  Raw₀.contains ⟨m.1, m.2.size_buckets_pos⟩ a

instance [BEq α] [Hashable α] : Membership α (DHashMap α β) where
  mem a m := m.contains a

instance [BEq α] [Hashable α] {m : DHashMap α β} {a : α} : Decidable (a ∈ m) :=
  show Decidable (m.contains a) from inferInstance

@[inline, inherit_doc Raw.get] def get [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap α β) (a : α) (h : a ∈ m) : β a :=
  Raw₀.get ⟨m.1, m.2.size_buckets_pos⟩ a h

@[inline, inherit_doc Raw.get!] def get! [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap α β) (a : α) [Inhabited (β a)] : β a :=
  Raw₀.get! ⟨m.1, m.2.size_buckets_pos⟩ a

@[inline, inherit_doc Raw.getD] def getD [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap α β) (a : α) (fallback : β a) : β a :=
  Raw₀.getD ⟨m.1, m.2.size_buckets_pos⟩ a fallback

@[inline, inherit_doc Raw.remove] def remove [BEq α] [Hashable α] (m : DHashMap α β) (a : α) : DHashMap α β :=
  ⟨Raw₀.remove ⟨m.1, m.2.size_buckets_pos⟩ a, .remove₀ m.2⟩

section

variable {β : Type v}

@[inline, inherit_doc Raw.Const.get?] def Const.get? [BEq α] [Hashable α] (m : DHashMap α (fun _ => β)) (a : α) : Option β :=
  Raw₀.Const.get? ⟨m.1, m.2.size_buckets_pos⟩ a

@[inline, inherit_doc Raw.Const.get] def Const.get [BEq α] [Hashable α] (m : DHashMap α (fun _ => β)) (a : α) (h : a ∈ m) : β :=
  Raw₀.Const.get ⟨m.1, m.2.size_buckets_pos⟩ a h

@[inline, inherit_doc Raw.Const.getD] def Const.getD [BEq α] [Hashable α] (m : DHashMap α (fun _ => β)) (a : α) (fallback : β) : β :=
  Raw₀.Const.getD ⟨m.1, m.2.size_buckets_pos⟩ a fallback

@[inline, inherit_doc Raw.Const.get!] def Const.get! [BEq α] [Hashable α] [Inhabited β] (m : DHashMap α (fun _ => β)) (a : α) : β :=
  Raw₀.Const.get! ⟨m.1, m.2.size_buckets_pos⟩ a

@[inline, inherit_doc Raw.Const.getThenInsertIfNew?] def Const.getThenInsertIfNew? [BEq α] [Hashable α] (m : DHashMap α (fun _ => β)) (a : α) (b : β) :
    Option β × DHashMap α (fun _ => β) :=
  let m' := Raw₀.Const.getThenInsertIfNew? ⟨m.1, m.2.size_buckets_pos⟩ a b
  ⟨m'.1, ⟨m'.2.1, .constGetThenInsertIfNew?₀ m.2⟩⟩

end

@[inline, inherit_doc Raw.size] def size [BEq α] [Hashable α] (m : DHashMap α β) : Nat :=
  m.1.size

@[inline, inherit_doc Raw.isEmpty] def isEmpty [BEq α] [Hashable α] (m : DHashMap α β) : Bool :=
  m.1.isEmpty

section Unverified

/-! We currently do not provide lemmas for the functions below. -/

@[inline, inherit_doc Raw.filter] def filter [BEq α] [Hashable α] (f : (a : α) → β a → Bool) (m : DHashMap α β) : DHashMap α β :=
  ⟨Raw₀.filter f ⟨m.1, m.2.size_buckets_pos⟩, .filter₀ m.2⟩

@[inline, inherit_doc Raw.foldlM] def foldlM [BEq α] [Hashable α] (f : δ → (a : α) → β a → m δ) (init : δ) (b : DHashMap α β) : m δ :=
  b.1.foldlM f init

@[inline, inherit_doc Raw.foldl] def foldl [BEq α] [Hashable α] (f : δ → (a : α) → β a → δ) (init : δ) (b : DHashMap α β) : δ :=
  b.1.foldl f init

@[inline, inherit_doc Raw.forM] def forM [BEq α] [Hashable α] (f : (a : α) → β a → m PUnit) (b : DHashMap α β) : m PUnit :=
  b.1.forM f

@[inline, inherit_doc Raw.forIn] def forIn [BEq α] [Hashable α] (f : (a : α) → β a → δ → m (ForInStep δ)) (init : δ) (b : DHashMap α β) : m δ :=
  b.1.forIn f init

instance [BEq α] [Hashable α] : ForM m (DHashMap α β) (Σ a, β a) where
  forM m f := m.forM (fun a b => f ⟨a, b⟩)

instance [BEq α] [Hashable α] : ForIn m (DHashMap α β) (Σ a, β a) where
  forIn m init f := m.forIn (fun a b acc => f ⟨a, b⟩ acc) init

@[inline, inherit_doc Raw.toList] def toList [BEq α] [Hashable α] (m : DHashMap α β) : List (Σ a, β a) :=
  m.1.toList

@[inline, inherit_doc Raw.toArray] def toArray [BEq α] [Hashable α] (m : DHashMap α β) : Array (Σ a, β a) :=
  m.1.toArray

@[inline, inherit_doc Raw.Const.toList] def Const.toList {β : Type v} [BEq α] [Hashable α] (m : DHashMap α (fun _ => β)) : List (α × β) :=
  Raw.Const.toList m.1

@[inline, inherit_doc Raw.Const.toArray] def Const.toArray {β : Type v} [BEq α] [Hashable α] (m : DHashMap α (fun _ => β)) : Array (α × β) :=
  Raw.Const.toArray m.1

@[inline, inherit_doc Raw.keys] def keys [BEq α] [Hashable α] (m : DHashMap α β) : List α :=
  m.1.keys

@[inline, inherit_doc Raw.keysArray] def keysArray [BEq α] [Hashable α] (m : DHashMap α β) : Array α :=
  m.1.keysArray

@[inline, inherit_doc Raw.values] def values {β : Type v} [BEq α] [Hashable α] (m : DHashMap α (fun _ => β)) : List β :=
  m.1.values

@[inline, inherit_doc Raw.insertMany] def insertMany [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] (m : DHashMap α β) (l : ρ) : DHashMap α β :=
  ⟨(Raw₀.insertMany ⟨m.1, m.2.size_buckets_pos⟩ l).1, (Raw₀.insertMany ⟨m.1, m.2.size_buckets_pos⟩ l).2 _ Raw.WF.insert₀ m.2⟩

@[inline, inherit_doc Raw.Const.insertMany] def Const.insertMany {β : Type v} [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ (α × β)] (m : DHashMap α (fun _ => β)) (l : ρ) : DHashMap α (fun _ => β) :=
  ⟨(Raw₀.Const.insertMany ⟨m.1, m.2.size_buckets_pos⟩ l).1, (Raw₀.Const.insertMany ⟨m.1, m.2.size_buckets_pos⟩ l).2 _ Raw.WF.insert₀ m.2⟩

@[inline, inherit_doc Raw.Const.insertManyUnit] def Const.insertManyUnit [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ α] (m : DHashMap α (fun _ => Unit)) (l : ρ) : DHashMap α (fun _ => Unit) :=
  ⟨(Raw₀.Const.insertManyUnit ⟨m.1, m.2.size_buckets_pos⟩ l).1, (Raw₀.Const.insertManyUnit ⟨m.1, m.2.size_buckets_pos⟩ l).2 _ Raw.WF.insert₀ m.2⟩

@[inline, inherit_doc Raw.ofList] def ofList [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] (l : ρ) : DHashMap α β :=
  insertMany ∅ l

@[inline, inherit_doc Raw.Const.ofList] def Const.ofList {β : Type v} [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ (α × β)] (l : ρ) : DHashMap α (fun _ => β) :=
  Const.insertMany ∅ l

@[inline, inherit_doc Raw.Const.unitOfList] def Const.unitOfList [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ α] (l : ρ) : DHashMap α (fun _ => Unit) :=
  Const.insertManyUnit ∅ l

@[inherit_doc Raw.Internal.numBuckets] def Internal.numBuckets [BEq α] [Hashable α] (m : DHashMap α β) : Nat :=
  Raw.Internal.numBuckets m.1

instance [BEq α] [Hashable α] [Repr α] [(a : α) → Repr (β a)] : Repr (DHashMap α β) where
  reprPrec m prec := Repr.addAppParen ("Std.DHashMap.ofList " ++ reprArg m.toList) prec

end Unverified

end Std.DHashMap
