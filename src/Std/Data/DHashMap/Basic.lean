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

This file develops the two types `Std.Data.DHashMap.Raw` and `Std.Data.DHashMap`. The difference between these
types is that the former does not bundle the well-formedness invariant and is thus safe to use in
nested inductive types. The well-formedness predicate is available as `Std.Data.DHashMap.Raw.WF` and this
file proves that all operations preserve well-formedness.

The operations `map` and `filterMap` on `Std.Data.DHashMap` are defined in the module `Std.Data.DHashMap.AdditionalOperations`.

Lemmas about the operations on `Std.Data.DHashMap.Raw` and `Std.Data.DHashMap` are available in the module
`Std.Data.DHashMap.Lemmas`.

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

@[inline] def empty (capacity := 8) : Raw α β :=
  (Raw₀.empty capacity).1

instance : EmptyCollection (Raw α β) where
  emptyCollection := empty

@[inline] def insert [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β a) : Raw α β :=
  if h : 0 < m.buckets.size then
    (Raw₀.insert ⟨m, h⟩ a b).1
  else m -- will never happen for well-formed inputs

@[inline] def insertIfNew [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β a) : Raw α β :=
  if h : 0 < m.buckets.size then
    (Raw₀.insertIfNew ⟨m, h⟩ a b).1
  else m -- will never happen for well-formed inputs

@[inline] def containsThenInsert [BEq α] [Hashable α] (m : Raw α β) (a : α) (b : β a) : Raw α β × Bool :=
  if h : 0 < m.buckets.size then
    let ⟨⟨r, _⟩, replaced⟩ := Raw₀.containsThenInsert ⟨m, h⟩ a b
    ⟨r, replaced⟩
  else (m, false) -- will never happen for well-formed inputs

@[inline] def getThenInsertIfNew? [BEq α] [Hashable α] [LawfulBEq α] (m : Raw α β) (a : α) (b : β a) : Raw α β × Option (β a) :=
  if h : 0 < m.buckets.size then
    let ⟨⟨r, _⟩, previous⟩ := Raw₀.getThenInsertIfNew? ⟨m, h⟩ a b
    ⟨r, previous⟩
  else (m, none) -- will never happen for well-formed inputs

@[inline] def get? [BEq α] [LawfulBEq α] [Hashable α] (m : Raw α β) (a : α) : Option (β a) :=
  if h : 0 < m.buckets.size then
    Raw₀.get? ⟨m, h⟩ a
  else none -- will never happen for well-formed inputs

@[inline] def contains [BEq α] [Hashable α] (m : Raw α β) (a : α) : Bool :=
  if h : 0 < m.buckets.size then
    Raw₀.contains ⟨m, h⟩ a
  else false -- will never happen for well-formed inputs

instance [BEq α] [Hashable α] : Membership α (Raw α β) where
  mem a m := m.contains a

instance [BEq α] [Hashable α] {m : Raw α β} {a : α} : Decidable (a ∈ m) :=
  show Decidable (m.contains a) from inferInstance

@[inline] def get [BEq α] [Hashable α] [LawfulBEq α] (m : Raw α β) (a : α) (h : a ∈ m) : β a :=
  Raw₀.get ⟨m, by change dite .. = true at h; split at h <;> simp_all⟩ a
    (by change dite .. = true at h; split at h <;> simp_all)

@[inline] def getD [BEq α] [Hashable α] [LawfulBEq α] (m : Raw α β) (a : α) (fallback : β a) : β a :=
  if h : 0 < m.buckets.size then
    Raw₀.getD ⟨m, h⟩ a fallback
  else fallback -- will never happen for well-formed inputs

@[inline] def get! [BEq α] [Hashable α] [LawfulBEq α] (m : Raw α β) (a : α) [Inhabited (β a)] : β a :=
  if h : 0 < m.buckets.size then
    Raw₀.get! ⟨m, h⟩ a
  else default -- will never happen for well-formed inputs

@[inline] def remove [BEq α] [Hashable α] (m : Raw α β) (a : α) : Raw α β :=
  if h : 0 < m.buckets.size then
    Raw₀.remove ⟨m, h⟩ a
  else m -- will never happen for well-formed inputs

section

variable {β : Type v}

@[inline] def Const.get? [BEq α] [Hashable α] (m : Raw α (fun _ => β)) (a : α) : Option β :=
  if h : 0 < m.buckets.size then
    Raw₀.Const.get? ⟨m, h⟩ a
  else none -- will never happen for well-formed inputs

@[inline] def Const.get [BEq α] [Hashable α] (m : Raw α (fun _ => β)) (a : α) (h : a ∈ m) : β :=
  Raw₀.Const.get ⟨m, by change dite .. = true at h; split at h <;> simp_all⟩ a
    (by change dite .. = true at h; split at h <;> simp_all)

@[inline] def Const.getD [BEq α] [Hashable α] (m : Raw α (fun _ => β)) (a : α) (fallback : β) : β :=
  if h : 0 < m.buckets.size then
    Raw₀.Const.getD ⟨m, h⟩ a fallback
  else fallback -- will never happen for well-formed inputs

@[inline] def Const.get! [BEq α] [Hashable α] [Inhabited β] (m : Raw α (fun _ => β)) (a : α) : β :=
  if h : 0 < m.buckets.size then
    Raw₀.Const.get! ⟨m, h⟩ a
  else default -- will never happen for well-formed inputs

@[inline] def Const.getThenInsertIfNew? [BEq α] [Hashable α] (m : Raw α (fun _ => β)) (a : α) (b : β) :
    Raw α (fun _ => β) × Option β :=
  if h : 0 < m.buckets.size then
    let ⟨⟨r, _⟩, replaced⟩ := Raw₀.Const.getThenInsertIfNew? ⟨m, h⟩ a b
    ⟨r, replaced⟩
  else (m, none) -- will never happen for well-formed inputs

end

@[inline] def isEmpty (m : Raw α β) : Bool :=
  m.size == 0

section Unverified

/-! We currently do not provide lemmas for the functions below. -/

@[inline] def filterMap {γ : α → Type w} (f : (a : α) → β a → Option (γ a)) (m : Raw α β) : Raw α γ :=
  if h : 0 < m.buckets.size then
    Raw₀.filterMap f ⟨m, h⟩
  else ∅ -- will never happen for well-formed inputs

@[inline] def map {γ : α → Type w} (f : (a : α) → β a → γ a) (m : Raw α β) : Raw α γ :=
  if h : 0 < m.buckets.size then
    Raw₀.map f ⟨m, h⟩
  else ∅ -- will never happen for well-formed inputs

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

@[inline] def forM (f : (a : α) → β a → m PUnit) (b : Raw α β) : m PUnit :=
  b.buckets.forM (AssocList.forM f)

@[inline] def forIn (f : (a : α) → β a → δ → m (ForInStep δ)) (init : δ) (b : Raw α β) : m δ :=
  b.buckets.forIn init (fun bucket acc => bucket.forInStep acc f)

instance : ForM m (Raw α β) (Σ a, β a) where
  forM m f := m.forM (fun a b => f ⟨a, b⟩)

instance : ForIn m (Raw α β) (Σ a, β a) where
  forIn m init f := m.forIn (fun a b acc => f ⟨a, b⟩ acc) init

@[inline] def toList (m : Raw α β) : List (Σ a, β a) :=
  m.foldl (fun acc k v => ⟨k, v⟩ :: acc) []

@[inline] def toArray (m : Raw α β) : Array (Σ a, β a) :=
  m.foldl (fun acc k v => acc.push ⟨k, v⟩) #[]

@[inline] def Const.toList {β : Type v} (m : Raw α (fun _ => β)) : List (α × β) :=
  m.foldl (fun acc k v => ⟨k, v⟩ :: acc) []

@[inline] def Const.toArray {β : Type v} (m : Raw α (fun _ => β)) : Array (α × β) :=
  m.foldl (fun acc k v => acc.push ⟨k, v⟩) #[]

@[inline] def keys (m : Raw α β) : List α :=
  m.foldl (fun acc k _ => k :: acc) []

@[inline] def keysArray (m : Raw α β) : Array α :=
  m.foldl (fun acc k _ => acc.push k) #[]

@[inline] def values {β : Type v} (m : Raw α (fun _ => β)) : List β :=
  m.foldl (fun acc _ v => v :: acc) []

@[inline] def insertMany [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] (m : Raw α β) (l : ρ) : Raw α β :=
  if h : 0 < m.buckets.size then
    (Raw₀.insertMany ⟨m, h⟩ l).1
else m -- will never happen for well-formed inputs

@[inline] def Const.insertMany {β : Type v} [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ (α × β)] (m : Raw α (fun _ => β)) (l : ρ) : Raw α (fun _ => β) :=
  if h : 0 < m.buckets.size then
    (Raw₀.Const.insertMany ⟨m, h⟩ l).1
  else m -- will never happen for well-formed inputs

@[inline] def Const.insertManyUnit [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ α] (m : Raw α (fun _ => Unit)) (l : ρ) : Raw α (fun _ => Unit) :=
  if h : 0 < m.buckets.size then
    (Raw₀.Const.insertManyUnit ⟨m, h⟩ l).1
  else m -- will never happen for well-formed inputs

@[inline] def ofList [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] (l : ρ) : Raw α β :=
  insertMany ∅ l

@[inline] def Const.ofList {β : Type v} [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ (α × β)] (l : ρ) : Raw α (fun _ => β) :=
  Const.insertMany ∅ l

@[inline] def Const.unitOfList [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ α] (l : ρ) : Raw α (fun _ => Unit) :=
  Const.insertManyUnit ∅ l

def Internal.numBuckets (m : Raw α β) : Nat :=
  m.buckets.size

end Unverified

section WF

/--
Well-formedness predicate for hash maps. Users of `DHashMap` will not need to interact with this. Users of `DHashMap.Raw`
will need to provide proofs of `WF` to lemmas and should use the lemmas `WF.empty`, `WF.emptyc`, `WF.insert`, `WF.containsThenInsert`,
`WF.remove`, `WF.insertIfNew`, `WF.getThenInsertIfNew?`, `WF.filter`, `WF.Const.getThenInsertIfNew?`, `WF.filterMap` and `WF.map` to
show that map operations preserve well-formedness.
-/
inductive WF : {α : Type u} → {β : α → Type v} → [BEq α] → [Hashable α] → Raw α β → Prop where
  -- Implementation note: the reason why we provide the `[EquivBEq α] [LawfulHashable α]` is so that we can write down
  -- `DHashMap.map` and `DHashMap.filterMap` in `AdditionalOperations.lean` without requiring these proofs just to invoke
  -- the operations.
  | wf {α β} [BEq α] [Hashable α] {m : Raw α β} : 0 < m.buckets.size → (∀ [EquivBEq α] [LawfulHashable α], Raw.WFImp m) → WF m
  | empty₀ {α β} [BEq α] [Hashable α] {c} : WF (Raw₀.empty c : Raw₀ α β).1
  | insert₀ {α β} [BEq α] [Hashable α] {m : Raw α β} {h a b} : WF m → WF (Raw₀.insert ⟨m, h⟩ a b).1
  | containsThenInsert₀ {α β} [BEq α] [Hashable α] {m : Raw α β} {h a b} : WF m → WF (Raw₀.containsThenInsert ⟨m, h⟩ a b).1.1
  | remove₀ {α β} [BEq α] [Hashable α] {m : Raw α β} {h a} : WF m → WF (Raw₀.remove ⟨m, h⟩ a).1
  | insertIfNew₀ {α β} [BEq α] [Hashable α] {m : Raw α β} {h a b} : WF m → WF (Raw₀.insertIfNew ⟨m, h⟩ a b).1
  | getThenInsertIfNew?₀ {α β} [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} {h a b} : WF m → WF (Raw₀.getThenInsertIfNew? ⟨m, h⟩ a b).1.1
  | filter₀ {α β} [BEq α] [Hashable α] {m : Raw α β} {h f} : WF m → WF (Raw₀.filter f ⟨m, h⟩).1
  | constGetThenInsertIfNew?₀ {α β} [BEq α] [Hashable α] {m : Raw α (fun _ => β)} {h a b} : WF m → WF (Raw₀.Const.getThenInsertIfNew? ⟨m, h⟩ a b).1.1

theorem WF.size_buckets_pos [BEq α] [Hashable α] (m : Raw α β) : WF m → 0 < m.buckets.size
  | wf h₁ _ => h₁
  | empty₀ => (Raw₀.empty _).2
  | insert₀ _ => (Raw₀.insert ⟨_, _⟩ _ _).2
  | containsThenInsert₀ _ => (Raw₀.containsThenInsert ⟨_, _⟩ _ _).1.2
  | remove₀ _ => (Raw₀.remove ⟨_, _⟩ _).2
  | insertIfNew₀ _ => (Raw₀.insertIfNew ⟨_, _⟩ _ _).2
  | getThenInsertIfNew?₀ _ => (Raw₀.getThenInsertIfNew? ⟨_, _⟩ _ _).1.2
  | filter₀ _ => (Raw₀.filter _ ⟨_, _⟩).2
  | constGetThenInsertIfNew?₀ _ => (Raw₀.Const.getThenInsertIfNew? ⟨_, _⟩ _ _).1.2

@[simp]
theorem WF.empty [BEq α] [Hashable α] {c : Nat} : (Raw.empty c : Raw α β).WF :=
  .empty₀

@[simp]
theorem WF.emptyc [BEq α] [Hashable α] : (∅ : Raw α β).WF :=
  .empty

theorem WF.insert [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β a} (h : m.WF) : (m.insert a b).WF := by
  simpa [Raw.insert, h.size_buckets_pos] using .insert₀ h

theorem WF.containsThenInsert [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β a} (h : m.WF) : (m.containsThenInsert a b).1.WF := by
  simpa [Raw.containsThenInsert, h.size_buckets_pos] using .containsThenInsert₀ h

theorem WF.remove [BEq α] [Hashable α] {m : Raw α β} {a : α} (h : m.WF) : (m.remove a).WF := by
  simpa [Raw.remove, h.size_buckets_pos] using .remove₀ h

theorem WF.insertIfNew [BEq α] [Hashable α] {m : Raw α β} {a : α} {b : β a} (h : m.WF) : (m.insertIfNew a b).WF := by
  simpa [Raw.insertIfNew, h.size_buckets_pos] using .insertIfNew₀ h

theorem WF.getThenInsertIfNew? [BEq α] [Hashable α] [LawfulBEq α] {m : Raw α β} {a : α} {b : β a} (h : m.WF) :
    (m.getThenInsertIfNew? a b).1.WF := by
  simpa [Raw.getThenInsertIfNew?, h.size_buckets_pos] using .getThenInsertIfNew?₀ h

theorem WF.filter [BEq α] [Hashable α] {m : Raw α β} {f : (a : α) → β a → Bool} (h : m.WF) :
    (m.filter f).WF := by
  simpa [Raw.filter, h.size_buckets_pos] using .filter₀ h

theorem WF.Const.getThenInsertIfNew? {β : Type v} [BEq α] [Hashable α] {m : Raw α (fun _ => β)} {a : α} {b : β} (h : m.WF) :
    (Const.getThenInsertIfNew? m a b).1.WF := by
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

def DHashMap (α : Type u) (β : α → Type v) [BEq α] [Hashable α] := { m : DHashMap.Raw α β // m.WF }

namespace DHashMap

/-- Constructs an empty hash map with a number of buckets appropriate for the given size. -/
@[inline] def empty [BEq α] [Hashable α] (capacity := 8) : DHashMap α β :=
  ⟨Raw.empty capacity, .empty₀⟩

instance [BEq α] [Hashable α] : EmptyCollection (DHashMap α β) where
  emptyCollection := empty

/--
Inserts the mapping into the map, replacing an existing mapping if there is one.
-/
@[inline] def insert [BEq α] [Hashable α] (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β :=
  ⟨Raw₀.insert ⟨m.1, m.2.size_buckets_pos⟩ a b, .insert₀ m.2⟩

@[inline] def insertIfNew [BEq α] [Hashable α] (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β :=
  ⟨Raw₀.insertIfNew ⟨m.1, m.2.size_buckets_pos⟩ a b, .insertIfNew₀ m.2⟩

/--
Inserts the mapping into the map, replacing an existing mapping if there is one.
Returns `true` if there was a previous mapping that was replaced.
-/
@[inline] def containsThenInsert [BEq α] [Hashable α] (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β × Bool :=
  let m' := Raw₀.containsThenInsert ⟨m.1, m.2.size_buckets_pos⟩ a b
  ⟨⟨m'.1.1, .containsThenInsert₀ m.2⟩, m'.2⟩

@[inline] def getThenInsertIfNew? [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap α β) (a : α) (b : β a) : DHashMap α β × Option (β a) :=
  let m' := Raw₀.getThenInsertIfNew? ⟨m.1, m.2.size_buckets_pos⟩ a b
  ⟨⟨m'.1.1, .getThenInsertIfNew?₀ m.2⟩, m'.2⟩

/--
Retrieves the value associated with the given key, if it exists. This function requires a `LawfulBEq` instance
to be able to cast the value to the correct type. If no such instance is available, you can use `getEntry?`,
`getWithCast?`,
or switch to a non-dependent `HashMap`.
-/
@[inline] def get? [BEq α] [LawfulBEq α] [Hashable α] (m : DHashMap α β) (a : α) : Option (β a) :=
  Raw₀.get? ⟨m.1, m.2.size_buckets_pos⟩ a

/-- Returns true if the hash map contains a mapping with a key equal to the given key. -/
@[inline] def contains [BEq α] [Hashable α] (m : DHashMap α β) (a : α) : Bool :=
  Raw₀.contains ⟨m.1, m.2.size_buckets_pos⟩ a

instance [BEq α] [Hashable α] : Membership α (DHashMap α β) where
  mem a m := m.contains a

instance [BEq α] [Hashable α] {m : DHashMap α β} {a : α} : Decidable (a ∈ m) :=
  show Decidable (m.contains a) from inferInstance

@[inline] def get [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap α β) (a : α) (h : a ∈ m) : β a :=
  Raw₀.get ⟨m.1, m.2.size_buckets_pos⟩ a h

@[inline] def get! [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap α β) (a : α) [Inhabited (β a)] : β a :=
  Raw₀.get! ⟨m.1, m.2.size_buckets_pos⟩ a

@[inline] def getD [BEq α] [Hashable α] [LawfulBEq α] (m : DHashMap α β) (a : α) (fallback : β a) : β a :=
  Raw₀.getD ⟨m.1, m.2.size_buckets_pos⟩ a fallback

/--
Removes the mapping with the given key if it exists.
-/
@[inline] def remove [BEq α] [Hashable α] (m : DHashMap α β) (a : α) : DHashMap α β :=
  ⟨Raw₀.remove ⟨m.1, m.2.size_buckets_pos⟩ a, .remove₀ m.2⟩

section

variable {β : Type v}

/--
Retrieves the value associated with the given key, if it exists. -/
@[inline] def Const.get? [BEq α] [Hashable α] (m : DHashMap α (fun _ => β)) (a : α) : Option β :=
  Raw₀.Const.get? ⟨m.1, m.2.size_buckets_pos⟩ a

@[inline] def Const.get [BEq α] [Hashable α] (m : DHashMap α (fun _ => β)) (a : α) (h : a ∈ m) : β :=
  Raw₀.Const.get ⟨m.1, m.2.size_buckets_pos⟩ a h

@[inline] def Const.getD [BEq α] [Hashable α] (m : DHashMap α (fun _ => β)) (a : α) (fallback : β) : β :=
  Raw₀.Const.getD ⟨m.1, m.2.size_buckets_pos⟩ a fallback

@[inline] def Const.get! [BEq α] [Hashable α] [Inhabited β] (m : DHashMap α (fun _ => β)) (a : α) : β :=
  Raw₀.Const.get! ⟨m.1, m.2.size_buckets_pos⟩ a

@[inline] def Const.getThenInsertIfNew? [BEq α] [Hashable α] (m : DHashMap α (fun _ => β)) (a : α) (b : β) :
    DHashMap α (fun _ => β) × Option β :=
  let m' := Raw₀.Const.getThenInsertIfNew? ⟨m.1, m.2.size_buckets_pos⟩ a b
  ⟨⟨m'.1.1, .constGetThenInsertIfNew?₀ m.2⟩, m'.2⟩

end

@[inline] def size [BEq α] [Hashable α] (m : DHashMap α β) : Nat :=
  m.1.size

@[inline] def isEmpty [BEq α] [Hashable α] (m : DHashMap α β) : Bool :=
  m.1.isEmpty

section Unverified

/-! We currently do not provide lemmas for the functions below. -/

@[inline] def filter [BEq α] [Hashable α] (f : (a : α) → β a → Bool) (m : DHashMap α β) : DHashMap α β :=
  ⟨Raw₀.filter f ⟨m.1, m.2.size_buckets_pos⟩, .filter₀ m.2⟩

@[inline] def foldlM [BEq α] [Hashable α] (f : δ → (a : α) → β a → m δ) (init : δ) (b : DHashMap α β) : m δ :=
  b.1.foldlM f init

@[inline] def foldl [BEq α] [Hashable α] (f : δ → (a : α) → β a → δ) (init : δ) (b : DHashMap α β) : δ :=
  b.1.foldl f init

@[inline] def forM [BEq α] [Hashable α] (f : (a : α) → β a → m PUnit) (b : DHashMap α β) : m PUnit :=
  b.1.forM f

@[inline] def forIn [BEq α] [Hashable α] (f : (a : α) → β a → δ → m (ForInStep δ)) (init : δ) (b : DHashMap α β) : m δ :=
  b.1.forIn f init

instance [BEq α] [Hashable α] : ForM m (DHashMap α β) (Σ a, β a) where
  forM m f := m.forM (fun a b => f ⟨a, b⟩)

instance [BEq α] [Hashable α] : ForIn m (DHashMap α β) (Σ a, β a) where
  forIn m init f := m.forIn (fun a b acc => f ⟨a, b⟩ acc) init

@[inline] def toList [BEq α] [Hashable α] (m : DHashMap α β) : List (Σ a, β a) :=
  m.1.toList

@[inline] def toArray [BEq α] [Hashable α] (m : DHashMap α β) : Array (Σ a, β a) :=
  m.1.toArray

@[inline] def Const.toList {β : Type v} [BEq α] [Hashable α] (m : DHashMap α (fun _ => β)) : List (α × β) :=
  Raw.Const.toList m.1

@[inline] def Const.toArray {β : Type v} [BEq α] [Hashable α] (m : DHashMap α (fun _ => β)) : Array (α × β) :=
  Raw.Const.toArray m.1

@[inline] def keys [BEq α] [Hashable α] (m : DHashMap α β) : List α :=
  m.1.keys

@[inline] def keysArray [BEq α] [Hashable α] (m : DHashMap α β) : Array α :=
  m.1.keysArray

@[inline] def values {β : Type v} [BEq α] [Hashable α] (m : DHashMap α (fun _ => β)) : List β :=
  m.1.values

@[inline] def insertMany [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] (m : DHashMap α β) (l : ρ) : DHashMap α β :=
  ⟨(Raw₀.insertMany ⟨m.1, m.2.size_buckets_pos⟩ l).1, (Raw₀.insertMany ⟨m.1, m.2.size_buckets_pos⟩ l).2 _ Raw.WF.insert₀ m.2⟩

@[inline] def Const.insertMany {β : Type v} [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ (α × β)] (m : DHashMap α (fun _ => β)) (l : ρ) : DHashMap α (fun _ => β) :=
  ⟨(Raw₀.Const.insertMany ⟨m.1, m.2.size_buckets_pos⟩ l).1, (Raw₀.Const.insertMany ⟨m.1, m.2.size_buckets_pos⟩ l).2 _ Raw.WF.insert₀ m.2⟩

@[inline] def Const.insertManyUnit [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ α] (m : DHashMap α (fun _ => Unit)) (l : ρ) : DHashMap α (fun _ => Unit) :=
  ⟨(Raw₀.Const.insertManyUnit ⟨m.1, m.2.size_buckets_pos⟩ l).1, (Raw₀.Const.insertManyUnit ⟨m.1, m.2.size_buckets_pos⟩ l).2 _ Raw.WF.insert₀ m.2⟩

@[inline] def ofList [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] (l : ρ) : DHashMap α β :=
  insertMany ∅ l

@[inline] def Const.ofList {β : Type v} [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ (α × β)] (l : ρ) : DHashMap α (fun _ => β) :=
  Const.insertMany ∅ l

@[inline] def Const.unitOfList [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ α] (l : ρ) : DHashMap α (fun _ => Unit) :=
  Const.insertManyUnit ∅ l

def Internal.numBuckets [BEq α] [Hashable α] (m : DHashMap α β) :=
  Raw.Internal.numBuckets m.1

end Unverified

end Std.DHashMap
