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

attribute [local instance] Std.DHashMap.isSetoid

universe u v w

variable {α : Type u} {β : α → Type v} {γ : α → Type w}

variable {_ : BEq α} {_ : Hashable α}

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
structure ExtDHashMap (α : Type u) (β : α → Type v) [BEq α] [Hashable α] where
  /-- Internal implementation detail of the hash map. -/
  mk' ::
  /-- Internal implementation detail of the hash map. -/
  inner : Quotient (DHashMap.isSetoid α β)

namespace ExtDHashMap

/-- Internal implementation detail of the hash map. -/
abbrev mk (m : DHashMap α β) : ExtDHashMap α β :=
  mk' (.mk _ m)

/-- Internal implementation detail of the hash map. -/
abbrev lift {γ : Sort w} (f : DHashMap α β → γ) (h : ∀ a b, a ~m b → f a = f b) (m : ExtDHashMap α β) : γ :=
  m.1.lift f h

/-- Internal implementation detail of the hash map. -/
abbrev pliftOn {γ : Sort w} (m : ExtDHashMap α β) (f : (a : DHashMap α β) → m = mk a → γ)
    (h : ∀ a b h₁ h₂, a ~m b → f a h₁ = f b h₂) : γ :=
  m.1.pliftOn (fun a ha => f a (by cases m; cases ha; rfl)) (fun _ _ _ _ h' => h _ _ _ _ h')

@[induction_eliminator, cases_eliminator, elab_as_elim]
theorem inductionOn {motive : ExtDHashMap α β → Prop} (m : ExtDHashMap α β)
    (mk : (a : DHashMap α β) → motive (mk a)) : motive m :=
  (m.1.inductionOn fun _ => mk _ : motive ⟨m.1⟩)

@[elab_as_elim]
theorem inductionOn₂ {motive : ExtDHashMap α β → ExtDHashMap α β → Prop}
    (m₁ m₂ : ExtDHashMap α β) (mk : (a b : DHashMap α β) → motive (mk a) (mk b)) : motive m₁ m₂ :=
  m₁.inductionOn fun _ => m₂.inductionOn fun _ => mk _ _

theorem sound {m₁ m₂ : DHashMap α β} (h : m₁ ~m m₂) : mk m₁ = mk m₂ :=
  congrArg mk' (Quotient.sound h)

theorem exact {m₁ m₂ : DHashMap α β} (h : mk m₁ = mk m₂) : m₁ ~m m₂ :=
  Quotient.exact (congrArg inner h)

@[inline, inherit_doc DHashMap.emptyWithCapacity]
def emptyWithCapacity [BEq α] [Hashable α]
    (capacity := 8) : ExtDHashMap α β :=
  mk (DHashMap.emptyWithCapacity capacity)

instance [BEq α] [Hashable α] : EmptyCollection (ExtDHashMap α β) where
  emptyCollection := emptyWithCapacity

instance [BEq α] [Hashable α] : Inhabited (ExtDHashMap α β) where
  default := ∅

@[inline, inherit_doc DHashMap.insert]
def insert [EquivBEq α] [LawfulHashable α] (m : ExtDHashMap α β) (a : α)
    (b : β a) : ExtDHashMap α β :=
  m.lift (fun m => mk (m.insert a b))
    (fun m m' (h : m ~m m') => sound (h.insert a b))

instance [EquivBEq α] [LawfulHashable α] : Singleton ((a : α) × β a) (ExtDHashMap α β) where
  singleton | ⟨a, b⟩ => (∅ : ExtDHashMap α β).insert a b

instance [EquivBEq α] [LawfulHashable α] : Insert ((a : α) × β a) (ExtDHashMap α β) where
  insert | ⟨a, b⟩, s => s.insert a b

instance [EquivBEq α] [LawfulHashable α] : LawfulSingleton ((a : α) × β a) (ExtDHashMap α β) :=
  ⟨fun _ => rfl⟩

@[inline, inherit_doc DHashMap.insertIfNew]
def insertIfNew [EquivBEq α] [LawfulHashable α] (m : ExtDHashMap α β)
    (a : α) (b : β a) : ExtDHashMap α β :=
  m.lift (fun m => mk (m.insertIfNew a b))
    (fun m m' (h : m ~m m') => sound (h.insertIfNew a b))

@[inline, inherit_doc DHashMap.containsThenInsert]
def containsThenInsert [EquivBEq α] [LawfulHashable α]
    (m : ExtDHashMap α β) (a : α) (b : β a) : Bool × ExtDHashMap α β :=
  m.lift (fun m => let m' := m.containsThenInsert a b; ⟨m'.1, mk m'.2⟩)
    (fun m m' (h : m ~m m') =>
      Prod.ext
        (m.containsThenInsert_fst.symm ▸ m'.containsThenInsert_fst.symm ▸ h.contains_eq)
        (sound <|
          m.containsThenInsert_snd.symm ▸ m'.containsThenInsert_snd.symm ▸ h.insert a b))

@[inline, inherit_doc DHashMap.containsThenInsertIfNew]
def containsThenInsertIfNew [EquivBEq α] [LawfulHashable α]
    (m : ExtDHashMap α β) (a : α) (b : β a) : Bool × ExtDHashMap α β :=
  m.lift (fun m => let m' := m.containsThenInsertIfNew a b; ⟨m'.1, mk m'.2⟩)
    (fun m m' (h : m ~m m') =>
      Prod.ext
        (m.containsThenInsertIfNew_fst.symm ▸ m'.containsThenInsertIfNew_fst.symm ▸ h.contains_eq)
        (sound <|
          m.containsThenInsertIfNew_snd.symm ▸ m'.containsThenInsertIfNew_snd.symm ▸ h.insertIfNew a b))

@[inline, inherit_doc DHashMap.getThenInsertIfNew?]
def getThenInsertIfNew? [LawfulBEq α]
    (m : ExtDHashMap α β) (a : α) (b : β a) : Option (β a) × ExtDHashMap α β :=
  m.lift (fun m => let m' := m.getThenInsertIfNew? a b; ⟨m'.1, mk m'.2⟩)
    (fun m m' (h : m ~m m') =>
      Prod.ext
        (m.getThenInsertIfNew?_fst.symm ▸ m'.getThenInsertIfNew?_fst.symm ▸ h.get?_eq)
        (sound <|
          m.getThenInsertIfNew?_snd.symm ▸ m'.getThenInsertIfNew?_snd.symm ▸ h.insertIfNew a b))

@[inline, inherit_doc DHashMap.get?]
def get? [LawfulBEq α] (m : ExtDHashMap α β)
    (a : α) : Option (β a) :=
  m.lift (fun m => m.get? a) (fun m m' (h : m ~m m') => h.get?_eq)

@[inline, inherit_doc DHashMap.contains]
def contains [EquivBEq α] [LawfulHashable α] (m : ExtDHashMap α β) (a : α) :
    Bool :=
  m.lift (fun m => m.contains a) (fun m m' (h : m ~m m') => h.contains_eq)

instance [EquivBEq α] [LawfulHashable α] : Membership α (ExtDHashMap α β) where
  mem m a := m.contains a

instance [EquivBEq α] [LawfulHashable α] {m : ExtDHashMap α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs <| Decidable (m.contains a)

@[inline, inherit_doc DHashMap.get]
def get [LawfulBEq α] (m : ExtDHashMap α β) (a : α)
    (h : a ∈ m) : β a :=
  m.pliftOn (fun m h' => m.get a (h' ▸ h :))
    (fun m m' _ _ (h : m ~m m') => h.get_eq _)

@[inline, inherit_doc DHashMap.get!]
def get! [LawfulBEq α] (m : ExtDHashMap α β)
    (a : α) [Inhabited (β a)] : β a :=
  m.lift (fun m => m.get! a) (fun m m' (h : m ~m m') => h.get!_eq)

@[inline, inherit_doc DHashMap.getD]
def getD [LawfulBEq α] (m : ExtDHashMap α β)
    (a : α) (fallback : β a) : β a :=
  m.lift (fun m => m.getD a fallback) (fun m m' (h : m ~m m') => h.getD_eq)

@[inline, inherit_doc DHashMap.erase]
def erase [EquivBEq α] [LawfulHashable α] (m : ExtDHashMap α β) (a : α) :
    ExtDHashMap α β :=
  m.lift (fun m => mk (m.erase a))
    (fun m m' (h : m ~m m') => sound (h.erase a))

namespace Const

variable {β : Type v}

@[inline, inherit_doc DHashMap.Const.get?]
def get? [EquivBEq α] [LawfulHashable α]
    (m : ExtDHashMap α (fun _ => β)) (a : α) : Option β :=
  m.lift (fun m => DHashMap.Const.get? m a)
    (fun m m' (h : m ~m m') => h.constGet?_eq)

@[inline, inherit_doc DHashMap.Const.get]
def get [EquivBEq α] [LawfulHashable α]
    (m : ExtDHashMap α (fun _ => β)) (a : α) (h : a ∈ m) : β :=
  m.pliftOn (fun m h' => DHashMap.Const.get m a (h' ▸ h :))
    (fun m m' _ _ (h : m ~m m') => h.constGet_eq _)

@[inline, inherit_doc DHashMap.Const.getD]
def getD [EquivBEq α] [LawfulHashable α]
    (m : ExtDHashMap α (fun _ => β)) (a : α) (fallback : β) : β :=
  m.lift (fun m => DHashMap.Const.getD m a fallback)
    (fun m m' (h : m ~m m') => h.constGetD_eq)

@[inline, inherit_doc DHashMap.Const.get!]
def get! [EquivBEq α] [LawfulHashable α] [Inhabited β]
    (m : ExtDHashMap α (fun _ => β)) (a : α) : β :=
  m.lift (fun m => DHashMap.Const.get! m a)
    (fun m m' (h : m ~m m') => h.constGet!_eq)

@[inline, inherit_doc DHashMap.Const.getThenInsertIfNew?]
def getThenInsertIfNew? [EquivBEq α] [LawfulHashable α]
    (m : ExtDHashMap α (fun _ => β)) (a : α) (b : β) :
    Option β × ExtDHashMap α (fun _ => β) :=
  m.lift (fun m =>
      let m' := DHashMap.Const.getThenInsertIfNew? m a b
      ⟨m'.1, mk m'.2⟩)
    (fun m m' (h : m ~m m') =>
      Prod.ext
        (DHashMap.Const.getThenInsertIfNew?_fst.symm ▸
          DHashMap.Const.getThenInsertIfNew?_fst.symm ▸ h.constGet?_eq)
        (sound <|
          DHashMap.Const.getThenInsertIfNew?_snd.symm ▸
          DHashMap.Const.getThenInsertIfNew?_snd.symm ▸ h.insertIfNew a b))

end Const

@[inline, inherit_doc DHashMap.getKey?]
def getKey? [EquivBEq α] [LawfulHashable α] (m : ExtDHashMap α β) (a : α) : Option α :=
  m.lift (fun m => m.getKey? a) (fun m m' (h : m ~m m') => h.getKey?_eq)

@[inline, inherit_doc DHashMap.getKey]
def getKey [EquivBEq α] [LawfulHashable α] (m : ExtDHashMap α β) (a : α) (h : a ∈ m) : α :=
  m.pliftOn (fun m h' => m.getKey a (h' ▸ h :))
    (fun m m' _ _ (h : m ~m m') => h.getKey_eq _)

@[inline, inherit_doc DHashMap.getKey!]
def getKey! [EquivBEq α] [LawfulHashable α] [Inhabited α] (m : ExtDHashMap α β) (a : α) : α :=
  m.lift (fun m => m.getKey! a) (fun m m' (h : m ~m m') => h.getKey!_eq)

@[inline, inherit_doc DHashMap.getKeyD]
def getKeyD [EquivBEq α] [LawfulHashable α] (m : ExtDHashMap α β) (a : α) (fallback : α) : α :=
  m.lift (fun m => m.getKeyD a fallback)
    (fun m m' (h : m ~m m') => h.getKeyD_eq)

@[inline, inherit_doc DHashMap.size]
def size [EquivBEq α] [LawfulHashable α] (m : ExtDHashMap α β) : Nat :=
  m.lift (fun m => m.size) (fun m m' (h : m ~m m') => h.size_eq)

@[inline, inherit_doc DHashMap.isEmpty]
def isEmpty [EquivBEq α] [LawfulHashable α] (m : ExtDHashMap α β) : Bool :=
  m.lift (fun m => m.isEmpty) (fun m m' (h : m ~m m') => h.isEmpty_eq)

-- TODO: add fold similar to `Finset.fold`

@[inline, inherit_doc DHashMap.filter]
def filter [EquivBEq α] [LawfulHashable α] (f : (a : α) → β a → Bool)
    (m : ExtDHashMap α β) : ExtDHashMap α β :=
  m.lift (fun m => mk (m.filter f))
    (fun m m' (h : m ~m m') => sound (h.filter f))

@[inline, inherit_doc DHashMap.map]
def map [EquivBEq α] [LawfulHashable α] (f : (a : α) → β a → γ a)
    (m : ExtDHashMap α β) : ExtDHashMap α γ :=
  m.lift (fun m => mk (m.map f))
    (fun m m' (h : m ~m m') => sound (h.map f))

@[inline, inherit_doc DHashMap.filterMap]
def filterMap [EquivBEq α] [LawfulHashable α] (f : (a : α) → β a → Option (γ a))
    (m : ExtDHashMap α β) : ExtDHashMap α γ :=
  m.lift (fun m => mk (m.filterMap f))
    (fun m m' (h : m ~m m') => sound (h.filterMap f))

@[inline, inherit_doc DHashMap.modify]
def modify [LawfulBEq α] (m : ExtDHashMap α β)
    (a : α) (f : β a → β a) : ExtDHashMap α β :=
  m.lift (fun m => mk (m.modify a f))
    (fun m m' (h : m ~m m') => sound (h.modify a f))

@[inline, inherit_doc DHashMap.Const.modify]
def Const.modify [EquivBEq α] [LawfulHashable α] {β : Type v} (m : ExtDHashMap α (fun _ => β))
    (a : α) (f : β → β) : ExtDHashMap α (fun _ => β) :=
  m.lift (fun m => mk (DHashMap.Const.modify m a f))
    (fun m m' (h : m ~m m') => sound (h.constModify a f))

@[inline, inherit_doc DHashMap.alter]
def alter [LawfulBEq α] (m : ExtDHashMap α β)
    (a : α) (f : Option (β a) → Option (β a)) : ExtDHashMap α β :=
  m.lift (fun m => mk (m.alter a f))
    (fun m m' (h : m ~m m') => sound (h.alter a f))

@[inline, inherit_doc DHashMap.Const.alter]
def Const.alter [EquivBEq α] [LawfulHashable α] {β : Type v} (m : ExtDHashMap α (fun _ => β))
    (a : α) (f : Option β → Option β) : ExtDHashMap α (fun _ => β) :=
  m.lift (fun m => mk (DHashMap.Const.alter m a f))
    (fun m m' (h : m ~m m') => sound (h.constAlter a f))

/-
Note: We can't use the existing functions because weird (noncomputable) `ForIn` instances
can break congruence. The subtype is still used to provide the `insertMany_ind` theorem.
-/

@[inline, inherit_doc DHashMap.insertMany]
def insertMany [EquivBEq α] [LawfulHashable α] {ρ : Type w}
    [ForIn Id ρ ((a : α) × β a)] (m : ExtDHashMap α β) (l : ρ) : ExtDHashMap α β := Id.run do
  let mut m : { x // ∀ P : ExtDHashMap α β → Prop,
    P m → (∀ {m a b}, P m → P (m.insert a b)) → P x } := ⟨m, fun _ h _ => h⟩
  for ⟨a, b⟩ in l do
    m := ⟨m.1.insert a b, fun _ init step => step (m.2 _ init step)⟩
  return m.1

@[inline, inherit_doc DHashMap.Const.insertMany]
def Const.insertMany [EquivBEq α] [LawfulHashable α] {β : Type v} {ρ : Type w}
    [ForIn Id ρ (α × β)] (m : ExtDHashMap α (fun _ => β))
    (l : ρ) : ExtDHashMap α (fun _ => β) := Id.run do
  let mut m : { x // ∀ P : ExtDHashMap α (fun _ => β) → Prop,
    P m → (∀ {m a b}, P m → P (m.insert a b)) → P x } := ⟨m, fun _ h _ => h⟩
  for (a, b) in l do
    m := ⟨m.1.insert a b, fun _ init step => step (m.2 _ init step)⟩
  return m.1

@[inline, inherit_doc DHashMap.Const.insertManyIfNewUnit]
def Const.insertManyIfNewUnit [EquivBEq α] [LawfulHashable α] {ρ : Type w}
    [ForIn Id ρ α] (m : ExtDHashMap α (fun _ => Unit))
    (l : ρ) : ExtDHashMap α (fun _ => Unit) := Id.run do
  let mut m : { x // ∀ P : ExtDHashMap α (fun _ => Unit) → Prop,
    P m → (∀ {m a}, P m → P (m.insertIfNew a ())) → P x } := ⟨m, fun _ h _ => h⟩
  for a in l do
    m := ⟨m.1.insertIfNew a (), fun _ init step => step (m.2 _ init step)⟩
  return m.1

-- TODO (after verification): partition, union

@[inline, inherit_doc DHashMap.Const.unitOfArray]
def Const.unitOfArray [BEq α] [Hashable α] (l : Array α) :
    ExtDHashMap α (fun _ => Unit) :=
  mk (DHashMap.Const.unitOfArray l)

@[inline, inherit_doc DHashMap.ofList]
def ofList [BEq α] [Hashable α] (l : List ((a : α) × β a)) :
    ExtDHashMap α β :=
  mk (DHashMap.ofList l)

@[inline, inherit_doc DHashMap.Const.ofList]
def Const.ofList {β : Type v} [BEq α] [Hashable α] (l : List (α × β)) :
    ExtDHashMap α (fun _ => β) :=
  mk (DHashMap.Const.ofList l)

@[inline, inherit_doc DHashMap.Const.unitOfList]
def Const.unitOfList [BEq α] [Hashable α] (l : List α) :
    ExtDHashMap α (fun _ => Unit) :=
  mk (DHashMap.Const.unitOfList l)

end ExtDHashMap

end Std
