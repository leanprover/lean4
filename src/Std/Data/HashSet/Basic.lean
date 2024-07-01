/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.HashMap.Basic

/-!
# Hash set

This file develops the two types `Std.Data.HashSet.Raw` and `Std.Data.HashSet`. The difference between these
types is that the former does not bundle the well-formedness invariant and is thus safe to use in
nested inductive types. The well-formedness predicate is available as `Std.Data.HashSet.Raw.WF` and this
file proves that all operations preserve well-formedness.

Lemmas about the operations on `Std.Data.HashSet.Raw` and `Std.Data.HashSet` are available in the module
`Std.Data.HashSet.Lemmas`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

variable {α : Type u}

namespace Std

namespace HashSet

structure Raw (α : Type u) where
  inner : HashMap.Raw α Unit

namespace Raw

@[inline] def empty (capacity := 8) : Raw α :=
  ⟨HashMap.Raw.empty capacity⟩

instance : EmptyCollection (Raw α) where
  emptyCollection := empty

@[inline] def insert [BEq α] [Hashable α] (m : Raw α) (a : α) : Raw α :=
  ⟨m.inner.insert a ()⟩

@[inline] def containsThenInsert [BEq α] [Hashable α] (m : Raw α) (a : α) : Raw α × Bool :=
  let ⟨r, replaced⟩ := m.inner.containsThenInsert a ()
  ⟨⟨r⟩, replaced⟩

@[inline] def contains [BEq α] [Hashable α] (m : Raw α) (a : α) : Bool :=
  m.inner.contains a

instance [BEq α] [Hashable α] : Membership α (Raw α) where
  mem a m := a ∈ m.inner

instance [BEq α] [Hashable α] {m : Raw α} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.inner))

@[inline] def remove [BEq α] [Hashable α] (m : Raw α) (a : α) : Raw α :=
  ⟨m.inner.remove a⟩

@[inline] def size (m : Raw α) : Nat :=
  m.inner.size

@[inline] def isEmpty (m : Raw α) : Bool :=
  m.inner.isEmpty

section Unverified

/-! We currently do not provide lemmas for the functions below. -/

@[inline] def filter [BEq α] [Hashable α] (f : α → Bool) (m : Raw α) : Raw α :=
  ⟨m.inner.filter fun a _ => f a⟩

@[inline] def foldlM {m : Type v → Type v} [Monad m] {β : Type v} (f : β → α → m β) (init : β) (b : Raw α) : m β :=
  b.inner.foldlM (fun b a _ => f b a) init

@[inline] def foldl {β : Type v} (f : β → α → β) (init : β) (m : Raw α) : β :=
  m.inner.foldl (fun b a _ => f b a) init

@[inline] def forM {m : Type v → Type v} [Monad m] (f : α → m PUnit) (b : Raw α) : m PUnit :=
  b.inner.forM (fun a _ => f a)

@[inline] def forIn {m : Type v → Type v} [Monad m] {β : Type v} (f : α → β → m (ForInStep β)) (init : β) (b : Raw α) : m β :=
  b.inner.forIn (fun a _ acc => f a acc) init

instance {m : Type v → Type v} : ForM m (Raw α) α where
  forM m f := m.forM f

instance {m : Type v → Type v} : ForIn m (Raw α) α where
  forIn m init f := m.forIn f init

@[inline] def toList (m : Raw α) : List α :=
  m.inner.keys

@[inline] def toArray (m : Raw α) : Array α :=
  m.inner.keysArray

@[inline] def insertMany [BEq α] [Hashable α] {ρ : Type v} [ForIn Id ρ α] (m : Raw α) (l : ρ) : Raw α :=
  ⟨m.inner.insertManyUnit l⟩

@[inline] def ofList [BEq α] [Hashable α] {ρ : Type v} [ForIn Id ρ α] (l : ρ) : Raw α :=
  ⟨HashMap.Raw.unitOfList l⟩

end Unverified

structure WF [BEq α] [Hashable α] (m : Raw α) : Prop where
  out : m.inner.WF

theorem WF.empty [BEq α] [Hashable α] {c} : (empty c : Raw α).WF :=
  ⟨HashMap.Raw.WF.empty⟩

theorem WF.emptyc [BEq α] [Hashable α] : (∅ : Raw α).WF :=
  ⟨HashMap.Raw.WF.empty⟩

theorem WF.insert [BEq α] [Hashable α] {m : Raw α} {a : α} (h : m.WF) : (m.insert a).WF :=
  ⟨HashMap.Raw.WF.insert h.out⟩

theorem WF.containsThenInsert [BEq α] [Hashable α] {m : Raw α} {a : α} (h : m.WF) : (m.containsThenInsert a).1.WF :=
  ⟨HashMap.Raw.WF.containsThenInsert h.out⟩

theorem WF.remove [BEq α] [Hashable α] {m : Raw α} {a : α} (h : m.WF) : (m.remove a).WF :=
  ⟨HashMap.Raw.WF.remove h.out⟩

theorem WF.filter [BEq α] [Hashable α] {m : Raw α} {f : α → Bool} (h : m.WF) : (m.filter f).WF :=
  ⟨HashMap.Raw.WF.filter h.out⟩

theorem WF.insertMany [BEq α] [Hashable α] {ρ : Type v} [ForIn Id ρ α] {m : Raw α} {l : ρ} (h : m.WF) : (m.insertMany l).WF :=
  ⟨HashMap.Raw.WF.insertManyUnit h.out⟩

theorem WF.ofList [BEq α] [Hashable α] {ρ : Type v} [ForIn Id ρ α] {l : ρ} : (ofList l : Raw α).WF :=
  ⟨HashMap.Raw.WF.unitOfList⟩

end Raw

end HashSet

structure HashSet (α : Type u) [BEq α] [Hashable α] where
  inner : HashMap α Unit

namespace HashSet

@[inline] def empty [BEq α] [Hashable α] (capacity := 8) : HashSet α :=
  ⟨HashMap.empty capacity⟩

instance [BEq α] [Hashable α] : EmptyCollection (HashSet α) where
  emptyCollection := empty

@[inline] def insert [BEq α] [Hashable α] (m : HashSet α) (a : α) : HashSet α :=
  ⟨m.inner.insert a ()⟩

@[inline] def containsThenInsert [BEq α] [Hashable α] (m : HashSet α) (a : α) : HashSet α × Bool :=
  let ⟨r, replaced⟩ := m.inner.containsThenInsert a ()
  ⟨⟨r⟩, replaced⟩

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

end Unverified

end HashSet

end Std
