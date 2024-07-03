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

This file develops the type `Std.Data.HashMap` of dependent hash maps.

The operations `map` and `filterMap` on `Std.Data.HashMap` are defined in the module
`Std.Data.HashMap.AdditionalOperations`.

Lemmas about the operations on `Std.Data.HashMap` are available in the
module `Std.Data.HashMap.Lemmas`.

See the module `Std.Data.HashMap.Raw` for a variant of this type which is safe to use in
nested inductive types.
-/

universe u v w

variable {α : Type u} {β : Type v}

namespace Std

structure HashMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  inner : DHashMap α (fun _ => β)

namespace HashMap

@[inline] def empty [BEq α] [Hashable α] (capacity := 8) : HashMap α β :=
  ⟨DHashMap.empty capacity⟩

instance [BEq α] [Hashable α] : EmptyCollection (HashMap α β) where
  emptyCollection := empty

@[inline] def insert [BEq α] [Hashable α] (m : HashMap α β) (a : α) (b : β) : HashMap α β :=
  ⟨m.inner.insert a b⟩

@[inline] def insertIfNew [BEq α] [Hashable α] (m : HashMap α β) (a : α) (b : β) : HashMap α β :=
  ⟨m.inner.insertIfNew a b⟩

@[inline] def containsThenInsert [BEq α] [Hashable α] (m : HashMap α β) (a : α) (b : β) : Bool × HashMap α β :=
  let ⟨replaced, r⟩ := m.inner.containsThenInsert a b
  ⟨replaced, ⟨r⟩⟩

@[inline] def getThenInsertIfNew? [BEq α] [Hashable α] (m : HashMap α β) (a : α) (b : β) : Option β × HashMap α β :=
  let ⟨previous, r⟩ := DHashMap.Const.getThenInsertIfNew? m.inner a b
  ⟨previous, ⟨r⟩⟩

@[inline] def get? [BEq α] [Hashable α] (m : HashMap α β) (a : α) : Option β :=
  DHashMap.Const.get? m.inner a

@[inline] def contains [BEq α] [Hashable α] (m : HashMap α β) (a : α) : Bool :=
  m.inner.contains a

instance [BEq α] [Hashable α] : Membership α (HashMap α β) where
  mem a m := a ∈ m.inner

instance [BEq α] [Hashable α] {m : HashMap α β} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.inner))

@[inline] def get [BEq α] [Hashable α] (m : HashMap α β) (a : α) (h : a ∈ m) : β :=
  DHashMap.Const.get m.inner a h

@[inline] def getD [BEq α] [Hashable α] (m : HashMap α β) (a : α) (fallback : β) : β :=
  DHashMap.Const.getD m.inner a fallback

@[inline] def get! [BEq α] [Hashable α] [Inhabited β] (m : HashMap α β) (a : α) : β :=
  DHashMap.Const.get! m.inner a

instance [BEq α] [Hashable α] : GetElem? (HashMap α β) α β (fun m a => a ∈ m) where
  getElem m a h := m.get a h
  getElem? m a := m.get? a
  getElem! m a := m.get! a

@[inline] def remove [BEq α] [Hashable α] (m : HashMap α β) (a : α) : HashMap α β :=
  ⟨m.inner.remove a⟩

@[inline] def size [BEq α] [Hashable α] (m : HashMap α β) : Nat :=
  m.inner.size

@[inline] def isEmpty [BEq α] [Hashable α] (m : HashMap α β) : Bool :=
  m.inner.isEmpty

section Unverified

/-! We currently do not provide lemmas for the functions below. -/

@[inline] def filter [BEq α] [Hashable α] (f : α → β → Bool) (m : HashMap α β) : HashMap α β :=
  ⟨m.inner.filter f⟩

@[inline] def foldlM [BEq α] [Hashable α] {m : Type w → Type w} [Monad m] {γ : Type w} (f : γ → α → β → m γ) (init : γ) (b : HashMap α β) : m γ :=
  b.inner.foldlM f init

@[inline] def foldl [BEq α] [Hashable α] {γ : Type w} (f : γ → α → β → γ) (init : γ) (b : HashMap α β) : γ :=
  b.inner.foldl f init

@[inline] def forM [BEq α] [Hashable α] {m : Type w → Type w} [Monad m] (f : (a : α) → β → m PUnit) (b : HashMap α β) : m PUnit :=
  b.inner.forM f

@[inline] def forIn [BEq α] [Hashable α] {m : Type w → Type w} [Monad m] {γ : Type w} (f : (a : α) → β → γ → m (ForInStep γ)) (init : γ) (b : HashMap α β) : m γ :=
  b.inner.forIn f init

instance [BEq α] [Hashable α] {m : Type w → Type w} : ForM m (HashMap α β) (α × β) where
  forM m f := m.forM (fun a b => f (a, b))

instance [BEq α] [Hashable α] {m : Type w → Type w} : ForIn m (HashMap α β) (α × β) where
  forIn m init f := m.forIn (fun a b acc => f (a, b) acc) init

@[inline] def toList [BEq α] [Hashable α] (m : HashMap α β) : List (α × β) :=
  DHashMap.Const.toList m.inner

@[inline] def toArray [BEq α] [Hashable α] (m : HashMap α β) : Array (α × β) :=
  DHashMap.Const.toArray m.inner

@[inline] def keys [BEq α] [Hashable α] (m : HashMap α β) : List α :=
  m.inner.keys

@[inline] def keysArray [BEq α] [Hashable α] (m : HashMap α β) : Array α :=
  m.inner.keysArray

@[inline] def values [BEq α] [Hashable α] (m : HashMap α β) : List β :=
  m.inner.values

@[inline] def insertMany [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ (α × β)] (m : HashMap α β) (l : ρ) : HashMap α β :=
  ⟨DHashMap.Const.insertMany m.inner l⟩

@[inline] def insertManyUnit [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ α] (m : HashMap α Unit) (l : ρ) : HashMap α Unit :=
  ⟨DHashMap.Const.insertManyUnit m.inner l⟩

@[inline] def ofList [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ (α × β)] (l : ρ) : HashMap α β :=
  ⟨DHashMap.Const.ofList l⟩

@[inline] def unitOfList [BEq α] [Hashable α] {ρ : Type w} [ForIn Id ρ α] (l : ρ) : HashMap α Unit :=
  ⟨DHashMap.Const.unitOfList l⟩

def Internal.numBuckets [BEq α] [Hashable α] (m : HashMap α β) : Nat :=
  DHashMap.Internal.numBuckets m.inner

instance [BEq α] [Hashable α] [Repr α] [Repr β] : Repr (HashMap α β) where
  reprPrec m prec := Repr.addAppParen ("Std.HashMap.ofList " ++ reprArg m.toList) prec

end Unverified

end Std.HashMap
