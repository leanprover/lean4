/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
prelude
import Std.Data.DHashMap.Lemmas

/-!
# Extensional dependent hash maps

This file develops the type `Std.ExtDHashMap` of extensional dependent hash maps.

Lemmas about the operations on `Std.ExtDHashMap` are available in the
module `Std.Data.ExtDHashMap.Lemmas`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w}

variable {_ : BEq α} {_ : Hashable α} {_ : EquivBEq α} {_ : LawfulHashable α}

open scoped Std.DHashMap

namespace Std

/--
Extensional dependent hash maps.

This is a simple separate-chaining hash table. The data of the hash map consists of a cached size
and an array of buckets, where each bucket is a linked list of key-value pais. The number of buckets
is always a power of two. The hash map doubles its size upon inserting an element such that the
number of elements is more than 75% of the number of buckets.

The hash table is backed by an `Array`. Users should make sure that the hash map is used linearly to
avoid expensive copies.

The hash map uses `==` (provided by the `BEq` typeclass) to compare keys and `hash` (provided by
the `Hashable` typeclass) to hash them. To ensure that the operations behave as expected, `==`
must be an equivalence relation and `a == b` must imply `hash a = hash b` (see also the
`EquivBEq` and `LawfulHashable` typeclasses). Both of these conditions are automatic if the BEq
instance is lawful, i.e., if `a == b` implies `a = b`.

In contrast to regular dependent hash maps, `Std.ExtDHashMap` offers several extensionality lemmas
and therefore has more lemmas about equality of hash maps. This however also makes it lose the
ability to iterate freely over the hash map.

These hash maps contain a bundled well-formedness invariant, which means that they cannot
be used in nested inductive types. For these use cases, `Std.DHashMap.Raw` and
`Std.DHashMap.Raw.WF` unbundle the invariant from the hash map. When in doubt, prefer
`DHashMap` over `DHashMap.Raw`.
-/
def ExtDHashMap (α : Type u) (β : α → Type v) [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] :=
  Quotient (DHashMap.isSetoid α β)

namespace ExtDHashMap

@[inline, inherit_doc DHashMap.emptyWithCapacity]
def emptyWithCapacity [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (capacity := 8) : ExtDHashMap α β :=
  Quotient.mk' (DHashMap.emptyWithCapacity capacity)

instance [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : EmptyCollection (ExtDHashMap α β) where
  emptyCollection := emptyWithCapacity

instance [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : Inhabited (DHashMap α β) where
  default := ∅

@[inline, inherit_doc DHashMap.insert] def insert (m : ExtDHashMap α β) (a : α)
    (b : β a) : ExtDHashMap α β :=
  m.lift (fun m => Quotient.mk' (m.insert a b))
    (fun m m' (h : m ~m m') => Quotient.sound (h.insert a b))

instance : Singleton ((a : α) × β a) (ExtDHashMap α β) := ⟨fun ⟨a, b⟩ => (∅ : ExtDHashMap α β).insert a b⟩

instance : Insert ((a : α) × β a) (ExtDHashMap α β) := ⟨fun ⟨a, b⟩ s => s.insert a b⟩

instance : LawfulSingleton ((a : α) × β a) (ExtDHashMap α β) :=
  ⟨fun _ => rfl⟩

@[inline, inherit_doc DHashMap.insertIfNew] def insertIfNew (m : ExtDHashMap α β)
    (a : α) (b : β a) : ExtDHashMap α β :=
  m.lift (fun m => Quotient.mk' (m.insertIfNew a b))
    (fun m m' (h : m ~m m') => Quotient.sound (h.insertIfNew a b))

@[inline, inherit_doc DHashMap.containsThenInsert] def containsThenInsert
    (m : ExtDHashMap α β) (a : α) (b : β a) : Bool × ExtDHashMap α β :=
  m.lift (fun m => let m' := m.containsThenInsert a b; ⟨m'.1, Quotient.mk' m'.2⟩)
    (fun m m' (h : m ~m m') =>
      Prod.ext
        (m.containsThenInsert_fst.symm ▸ m'.containsThenInsert_fst.symm ▸ h.contains_eq)
        (Quotient.sound <|
          m.containsThenInsert_snd.symm ▸ m'.containsThenInsert_snd.symm ▸ h.insert a b))

@[inline, inherit_doc DHashMap.containsThenInsert] def containsThenInsertIfNew
    (m : ExtDHashMap α β) (a : α) (b : β a) : Bool × ExtDHashMap α β :=
  m.lift (fun m => let m' := m.containsThenInsertIfNew a b; ⟨m'.1, Quotient.mk' m'.2⟩)
    (fun m m' (h : m ~m m') =>
      Prod.ext
        (m.containsThenInsertIfNew_fst.symm ▸ m'.containsThenInsertIfNew_fst.symm ▸ h.contains_eq)
        (Quotient.sound <|
          m.containsThenInsertIfNew_snd.symm ▸ m'.containsThenInsertIfNew_snd.symm ▸ h.insertIfNew a b))

@[inline, inherit_doc DHashMap.getThenInsertIfNew?] def getThenInsertIfNew? [LawfulBEq α]
    (m : ExtDHashMap α β) (a : α) (b : β a) : Option (β a) × ExtDHashMap α β :=
  m.lift (fun m => let m' := m.getThenInsertIfNew? a b; ⟨m'.1, Quotient.mk' m'.2⟩)
    (fun m m' (h : m ~m m') =>
      Prod.ext
        (m.getThenInsertIfNew?_fst.symm ▸ m'.getThenInsertIfNew?_fst.symm ▸ h.get?_eq)
        (Quotient.sound <|
          m.getThenInsertIfNew?_snd.symm ▸ m'.getThenInsertIfNew?_snd.symm ▸ h.insertIfNew a b))

@[inline, inherit_doc DHashMap.get?] def get? [LawfulBEq α] (m : ExtDHashMap α β)
    (a : α) : Option (β a) :=
  m.lift (fun m => m.get? a) (fun m m' (h : m ~m m') => h.get?_eq)

@[inline, inherit_doc DHashMap.contains] def contains (m : ExtDHashMap α β) (a : α) :
    Bool :=
  m.lift (fun m => m.contains a) (fun m m' (h : m ~m m') => h.contains_eq)

instance : Membership α (ExtDHashMap α β) where
  mem m a := m.contains a

instance {m : ExtDHashMap α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs <| Decidable (m.contains a)

@[inline, inherit_doc DHashMap.get] def get [LawfulBEq α] (m : ExtDHashMap α β) (a : α)
    (h : a ∈ m) : β a :=
  m.pliftOn (fun m h' => m.get a (h' ▸ h :))
    (fun m m' _ _ (h : m ~m m') => h.get_eq _)

@[inline, inherit_doc DHashMap.get!] def get! [LawfulBEq α] (m : ExtDHashMap α β)
    (a : α) [Inhabited (β a)] : β a :=
  m.lift (fun m => m.get! a) (fun m m' (h : m ~m m') => h.get!_eq)

@[inline, inherit_doc DHashMap.getD] def getD [LawfulBEq α] (m : ExtDHashMap α β)
    (a : α) (fallback : β a) : β a :=
  m.lift (fun m => m.getD a fallback) (fun m m' (h : m ~m m') => h.getD_eq)

@[inline, inherit_doc DHashMap.erase] def erase (m : ExtDHashMap α β) (a : α) :
    ExtDHashMap α β :=
  m.lift (fun m => Quotient.mk' (m.erase a))
    (fun m m' (h : m ~m m') => Quotient.sound (h.erase a))

namespace Const

variable {β : Type v}

@[inline, inherit_doc DHashMap.Const.get?] def get?
    (m : ExtDHashMap α (fun _ => β)) (a : α) : Option β :=
  m.lift (fun m => DHashMap.Const.get? m a)
    (fun m m' (h : m ~m m') => h.constGet?_eq)

@[inline, inherit_doc DHashMap.Const.get] def get
    (m : ExtDHashMap α (fun _ => β)) (a : α) (h : a ∈ m) : β :=
  m.pliftOn (fun m h' => DHashMap.Const.get m a (h' ▸ h :))
    (fun m m' _ _ (h : m ~m m') => h.constGet_eq _)

@[inline, inherit_doc DHashMap.Const.getD] def getD
    (m : ExtDHashMap α (fun _ => β)) (a : α) (fallback : β) : β :=
  m.lift (fun m => DHashMap.Const.getD m a fallback)
    (fun m m' (h : m ~m m') => h.constGetD_eq)

@[inline, inherit_doc DHashMap.Const.get!] def get! [Inhabited β]
    (m : ExtDHashMap α (fun _ => β)) (a : α) : β :=
  m.lift (fun m => DHashMap.Const.get! m a)
    (fun m m' (h : m ~m m') => h.constGet!_eq)

@[inline, inherit_doc DHashMap.Const.getThenInsertIfNew?] def getThenInsertIfNew?
    (m : ExtDHashMap α (fun _ => β)) (a : α) (b : β) :
    Option β × ExtDHashMap α (fun _ => β) :=
  m.lift (fun m =>
      let m' := DHashMap.Const.getThenInsertIfNew? m a b
      ⟨m'.1, Quotient.mk' m'.2⟩)
    (fun m m' (h : m ~m m') =>
      Prod.ext
        (DHashMap.Const.getThenInsertIfNew?_fst.symm ▸
          DHashMap.Const.getThenInsertIfNew?_fst.symm ▸ h.constGet?_eq)
        (Quotient.sound <|
          DHashMap.Const.getThenInsertIfNew?_snd.symm ▸
          DHashMap.Const.getThenInsertIfNew?_snd.symm ▸ h.insertIfNew a b))

end Const

@[inline, inherit_doc DHashMap.getKey?] def getKey? (m : ExtDHashMap α β) (a : α) : Option α :=
  m.lift (fun m => m.getKey? a) (fun m m' (h : m ~m m') => h.getKey?_eq)

@[inline, inherit_doc DHashMap.getKey] def getKey (m : ExtDHashMap α β) (a : α) (h : a ∈ m) : α :=
  m.pliftOn (fun m h' => m.getKey a (h' ▸ h :))
    (fun m m' _ _ (h : m ~m m') => h.getKey_eq _)

@[inline, inherit_doc DHashMap.getKey!] def getKey! [Inhabited α] (m : ExtDHashMap α β) (a : α) : α :=
  m.lift (fun m => m.getKey! a) (fun m m' (h : m ~m m') => h.getKey!_eq)

@[inline, inherit_doc DHashMap.getKeyD] def getKeyD (m : ExtDHashMap α β) (a : α) (fallback : α) : α :=
  m.lift (fun m => m.getKeyD a fallback)
    (fun m m' (h : m ~m m') => h.getKeyD_eq)

@[inline, inherit_doc DHashMap.size] def size (m : ExtDHashMap α β) : Nat :=
  m.lift (fun m => m.size) (fun m m' (h : m ~m m') => h.size_eq)

@[inline, inherit_doc DHashMap.isEmpty] def isEmpty (m : ExtDHashMap α β) : Bool :=
  m.lift (fun m => m.isEmpty) (fun m m' (h : m ~m m') => h.isEmpty_eq)

-- TODO: add fold similar to `Finset.fold`

@[inline, inherit_doc DHashMap.filter] def filter (f : (a : α) → β a → Bool)
    (m : ExtDHashMap α β) : ExtDHashMap α β :=
  m.lift (fun m => Quotient.mk' (m.filter f))
    (fun m m' (h : m ~m m') => Quotient.sound (h.filter f))

@[inline, inherit_doc DHashMap.map] def map (f : (a : α) → β a → γ a)
    (m : ExtDHashMap α β) : ExtDHashMap α γ :=
  m.lift (fun m => Quotient.mk' (m.map f))
    (fun m m' (h : m ~m m') => Quotient.sound (h.map f))

@[inline, inherit_doc DHashMap.filterMap] def filterMap (f : (a : α) → β a → Option (γ a))
    (m : ExtDHashMap α β) : ExtDHashMap α γ :=
  m.lift (fun m => Quotient.mk' (m.filterMap f))
    (fun m m' (h : m ~m m') => Quotient.sound (h.filterMap f))

@[inline, inherit_doc DHashMap.modify] def modify [LawfulBEq α] (m : ExtDHashMap α β)
    (a : α) (f : β a → β a) : ExtDHashMap α β :=
  m.lift (fun m => Quotient.mk' (m.modify a f))
    (fun m m' (h : m ~m m') => Quotient.sound (h.modify a f))

@[inline, inherit_doc DHashMap.modify] def Const.modify {β : Type v} (m : ExtDHashMap α (fun _ => β))
    (a : α) (f : β → β) : ExtDHashMap α (fun _ => β) :=
  m.lift (fun m => Quotient.mk' (DHashMap.Const.modify m a f))
    (fun m m' (h : m ~m m') => Quotient.sound (h.constModify a f))

@[inline, inherit_doc DHashMap.alter] def alter [LawfulBEq α] (m : ExtDHashMap α β)
    (a : α) (f : Option (β a) → Option (β a)) : ExtDHashMap α β :=
  m.lift (fun m => Quotient.mk' (m.alter a f))
    (fun m m' (h : m ~m m') => Quotient.sound (h.alter a f))

@[inline, inherit_doc DHashMap.alter] def Const.alter {β : Type v} (m : ExtDHashMap α (fun _ => β))
    (a : α) (f : Option β → Option β) : ExtDHashMap α (fun _ => β) :=
  m.lift (fun m => Quotient.mk' (DHashMap.Const.alter m a f))
    (fun m m' (h : m ~m m') => Quotient.sound (h.constAlter a f))

/-
Note: We can't use the existing functions because weird (noncomputable) `ForIn` instances
can break congruence. The subtype is still used to provide the `insertMany_ind` theorem.
-/

@[inline, inherit_doc DHashMap.insertMany] def insertMany {ρ : Type w}
    [ForIn Id ρ ((a : α) × β a)] (m : ExtDHashMap α β) (l : ρ) : ExtDHashMap α β := Id.run do
  let mut m : { x // ∀ P : ExtDHashMap α β → Prop,
    P m → (∀ {m a b}, P m → P (m.insert a b)) → P x } := ⟨m, fun _ h _ => h⟩
  for ⟨a, b⟩ in l do
    m := ⟨m.1.insert a b, fun _ init step => step (m.2 _ init step)⟩
  return m.1

@[inline, inherit_doc DHashMap.Const.insertMany] def Const.insertMany {β : Type v} {ρ : Type w}
    [ForIn Id ρ (α × β)] (m : ExtDHashMap α (fun _ => β))
    (l : ρ) : ExtDHashMap α (fun _ => β) := Id.run do
  let mut m : { x // ∀ P : ExtDHashMap α (fun _ => β) → Prop,
    P m → (∀ {m a b}, P m → P (m.insert a b)) → P x } := ⟨m, fun _ h _ => h⟩
  for (a, b) in l do
    m := ⟨m.1.insert a b, fun _ init step => step (m.2 _ init step)⟩
  return m.1

@[inline, inherit_doc DHashMap.Const.insertManyIfNewUnit] def Const.insertManyIfNewUnit {ρ : Type w}
    [ForIn Id ρ α] (m : ExtDHashMap α (fun _ => Unit))
    (l : ρ) : ExtDHashMap α (fun _ => Unit) := Id.run do
  let mut m : { x // ∀ P : ExtDHashMap α (fun _ => Unit) → Prop,
    P m → (∀ {m a}, P m → P (m.insertIfNew a ())) → P x } := ⟨m, fun _ h _ => h⟩
  for a in l do
    m := ⟨m.1.insertIfNew a (), fun _ init step => step (m.2 _ init step)⟩
  return m.1

-- TODO (after verification): partition, union

/-
Note: we could use `ofList` here but we want the connection of `ofList` and `insertMany`.
-/

@[inline, inherit_doc DHashMap.ofList] def ofList
    [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (l : List ((a : α) × β a)) :
    ExtDHashMap α β :=
  insertMany ∅ l

@[inline, inherit_doc DHashMap.Const.ofList] def Const.ofList {β : Type v}
    [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (l : List (α × β)) :
    ExtDHashMap α (fun _ => β) :=
  Const.insertMany ∅ l

@[inline, inherit_doc DHashMap.Const.unitOfList] def Const.unitOfList
    [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] (l : List α) :
    ExtDHashMap α (fun _ => Unit) :=
  Const.insertManyIfNewUnit ∅ l

end ExtDHashMap

end Std
