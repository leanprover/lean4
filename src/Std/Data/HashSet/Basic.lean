/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.HashMap.Basic

/-!
# Hash sets

This file develops the type `Std.Data.HashSet` of dependent hash sets.

The operations `map` and `filterMap` on `Std.Data.HashSet` are defined in the module
`Std.Data.HashSet.AdditionalOperations`.

Lemmas about the operations on `Std.Data.HashSet` are available in the
module `Std.Data.HashSet.Lemmas`.

See the module `Std.Data.HashSet.Raw` for a variant of this type which is safe to use in
nested inductive types.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

variable {α : Type u}

namespace Std

structure HashSet (α : Type u) [BEq α] [Hashable α] where
  inner : HashMap α Unit

namespace HashSet

@[inline] def empty [BEq α] [Hashable α] (capacity := 8) : HashSet α :=
  ⟨HashMap.empty capacity⟩

instance [BEq α] [Hashable α] : EmptyCollection (HashSet α) where
  emptyCollection := empty

@[inline] def insert [BEq α] [Hashable α] (m : HashSet α) (a : α) : HashSet α :=
  ⟨m.inner.insert a ()⟩

@[inline] def containsThenInsert [BEq α] [Hashable α] (m : HashSet α) (a : α) : Bool × HashSet α :=
  let ⟨replaced, r⟩ := m.inner.containsThenInsert a ()
  ⟨replaced, ⟨r⟩⟩

@[inline] def contains [BEq α] [Hashable α] (m : HashSet α) (a : α) : Bool :=
  m.inner.contains a

instance [BEq α] [Hashable α] : Membership α (HashSet α) where
  mem a m := a ∈ m.inner

instance [BEq α] [Hashable α] {m : HashSet α} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.inner))

@[inline] def remove [BEq α] [Hashable α] (m : HashSet α) (a : α) : HashSet α :=
  ⟨m.inner.remove a⟩

@[inline] def size [BEq α] [Hashable α] (m : HashSet α) : Nat :=
  m.inner.size

@[inline] def isEmpty [BEq α] [Hashable α] (m : HashSet α) : Bool :=
  m.inner.isEmpty

section Unverified

/-! We currently do not provide lemmas for the functions below. -/

@[inline] def filter [BEq α] [Hashable α] (f : α → Bool) (m : HashSet α) : HashSet α :=
  ⟨m.inner.filter fun a _ => f a⟩

@[inline] def foldlM [BEq α] [Hashable α] {m : Type v → Type v} [Monad m] {β : Type v} (f : β → α → m β) (init : β) (b : HashSet α) : m β :=
  b.inner.foldlM (fun b a _ => f b a) init

@[inline] def foldl [BEq α] [Hashable α] {β : Type v} (f : β → α → β) (init : β) (m : HashSet α) : β :=
  m.inner.foldl (fun b a _ => f b a) init

@[inline] def forM [BEq α] [Hashable α] {m : Type v → Type v} [Monad m] (f : α → m PUnit) (b : HashSet α) : m PUnit :=
  b.inner.forM (fun a _ => f a)

@[inline] def forIn [BEq α] [Hashable α] {m : Type v → Type v} [Monad m] {β : Type v} (f : α → β → m (ForInStep β)) (init : β) (b : HashSet α) : m β :=
  b.inner.forIn (fun a _ acc => f a acc) init

instance [BEq α] [Hashable α] {m : Type v → Type v} : ForM m (HashSet α) α where
  forM m f := m.forM f

instance [BEq α] [Hashable α] {m : Type v → Type v} : ForIn m (HashSet α) α where
  forIn m init f := m.forIn f init

@[inline] def toList [BEq α] [Hashable α] (m : HashSet α) : List α :=
  m.inner.keys

@[inline] def toArray [BEq α] [Hashable α] (m : HashSet α) : Array α :=
  m.inner.keysArray

@[inline] def insertMany [BEq α] [Hashable α] {ρ : Type v} [ForIn Id ρ α] (m : HashSet α) (l : ρ) : HashSet α :=
  ⟨m.inner.insertManyUnit l⟩

@[inline] def ofList [BEq α] [Hashable α] {ρ : Type v} [ForIn Id ρ α] (l : ρ) : HashSet α :=
  ⟨HashMap.unitOfList l⟩

def Internal.numBuckets [BEq α] [Hashable α] (m : HashSet α) : Nat :=
  HashMap.Internal.numBuckets m.inner

instance [BEq α] [Hashable α] [Repr α] : Repr (HashSet α) where
  reprPrec m prec := Repr.addAppParen ("Std.HashSet.ofList " ++ reprArg m.toList) prec

end Unverified

end HashSet

end Std
