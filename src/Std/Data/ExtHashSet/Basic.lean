/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Std.Data.ExtHashMap.Basic

@[expose] public section

/-!
# Extensional hash sets

This module develops the type `Std.ExtHashSet` of extensional hash sets.

Lemmas about the operations on `Std.ExtHashSet` are available in the
module `Std.Data.ExtHashSet.Lemmas`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

variable {α : Type u} {_ : BEq α} {_ : Hashable α}

namespace Std

/--
Hash sets.

This is a simple separate-chaining hash table. The data of the hash set consists of a cached size
and an array of buckets, where each bucket is a linked list of keys. The number of buckets
is always a power of two. The hash set doubles its size upon inserting an element such that the
number of elements is more than 75% of the number of buckets.

The hash table is backed by an `Array`. Users should make sure that the hash set is used linearly to
avoid expensive copies.

The hash set uses `==` (provided by the `BEq` typeclass) to compare elements and `hash` (provided by
the `Hashable` typeclass) to hash them. To ensure that the operations behave as expected, `==`
should be an equivalence relation and `a == b` should imply `hash a = hash b` (see also the
`EquivBEq` and `LawfulHashable` typeclasses). Both of these conditions are automatic if the BEq
instance is lawful, i.e., if `a == b` implies `a = b`.

In contrast to regular hash sets, `Std.ExtHashSet` offers several extensionality lemmas
and therefore has more lemmas about equality of hash maps. This however also makes it lose the
ability to iterate freely over hash sets.

These hash sets contain a bundled well-formedness invariant, which means that they cannot
be used in nested inductive types. For these use cases, `Std.HashSet.Raw` and
`Std.HashSet.Raw.WF` unbundle the invariant from the hash set. When in doubt, prefer
`HashSet` or `ExtHashSet` over `HashSet.Raw`.
-/
structure ExtHashSet (α : Type u) [BEq α] [Hashable α] where
  /-- Internal implementation detail of the hash set. -/
  inner : ExtHashMap α Unit

namespace ExtHashSet

/--
Creates a new empty hash set. The optional parameter `capacity` can be supplied to presize the
set so that it can hold the given number of elements without reallocating. It is also possible to
use the empty collection notations `∅` and `{}` to create an empty hash set with the default
capacity.
-/
@[inline] def emptyWithCapacity [BEq α] [Hashable α] (capacity := 8) : ExtHashSet α :=
  ⟨ExtHashMap.emptyWithCapacity capacity⟩

instance [BEq α] [Hashable α] : EmptyCollection (ExtHashSet α) where
  emptyCollection := emptyWithCapacity

instance [BEq α] [Hashable α] : Inhabited (ExtHashSet α) where
  default := ∅

/--
Inserts the given element into the set. If the hash set already contains an element that is
equal (with regard to `==`) to the given element, then the hash set is returned unchanged.

Note: this non-replacement behavior is true for `ExtHashSet` and `ExtHashSet.Raw`.
The `insert` function on `ExtHashMap`, `DExtHashMap`, `ExtHashMap.Raw` and `DExtHashMap.Raw` behaves
differently: it will overwrite an existing mapping.
-/
@[inline] def insert [EquivBEq α] [LawfulHashable α] (m : ExtHashSet α) (a : α) : ExtHashSet α :=
  ⟨m.inner.insertIfNew a ()⟩

instance [EquivBEq α] [LawfulHashable α] : Singleton α (ExtHashSet α) where
  singleton a := (∅ : ExtHashSet α).insert a

instance [EquivBEq α] [LawfulHashable α] : Insert α (ExtHashSet α) where
  insert a s := s.insert a

/--
Checks whether an element is present in a set and inserts the element if it was not found.
If the hash set already contains an element that is equal (with regard to `==`) to the given
element, then the hash set is returned unchanged.

Equivalent to (but potentially faster than) calling `contains` followed by `insert`.
-/
@[inline]
def containsThenInsert [EquivBEq α] [LawfulHashable α] (m : ExtHashSet α)
    (a : α) : Bool × ExtHashSet α :=
  let ⟨replaced, r⟩ := m.inner.containsThenInsertIfNew a ()
  ⟨replaced, ⟨r⟩⟩

/--
Returns `true` if the given key is present in the set. There is also a `Prop`-valued version of
this: `a ∈ m` is equivalent to `m.contains a = true`.

Observe that this is different behavior than for lists: for lists, `∈` uses `=` and `contains` use
`==` for comparisons, while for hash sets, both use `==`.
-/
@[inline] def contains [EquivBEq α] [LawfulHashable α] (m : ExtHashSet α) (a : α) : Bool :=
  m.inner.contains a

instance [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α] : Membership α (ExtHashSet α) where
  mem m a := a ∈ m.inner

instance [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : ExtHashSet α} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.inner))

/-- Removes the element if it exists. -/
@[inline] def erase [EquivBEq α] [LawfulHashable α] (m : ExtHashSet α) (a : α) : ExtHashSet α :=
  ⟨m.inner.erase a⟩

/-- The number of elements present in the set -/
@[inline] def size [EquivBEq α] [LawfulHashable α] (m : ExtHashSet α) : Nat :=
  m.inner.size

/--
Checks if given key is contained and returns the key if it is, otherwise `none`.
The result in the `some` case is guaranteed to be pointer equal to the key in the set.
-/
@[inline] def get? [EquivBEq α] [LawfulHashable α] (m : ExtHashSet α) (a : α) : Option α :=
  m.inner.getKey? a

/--
Retrieves the key from the set that matches `a`. Ensures that such a key exists by requiring a proof
of `a ∈ m`. The result is guaranteed to be pointer equal to the key in the set.
-/
@[inline] def get [EquivBEq α] [LawfulHashable α]
    (m : ExtHashSet α) (a : α) (h : a ∈ m) : α :=
  m.inner.getKey a h

/--
Checks if given key is contained and returns the key if it is, otherwise `fallback`.
If they key is contained the result is guaranteed to be pointer equal to the key in the set.
-/
@[inline] def getD [EquivBEq α] [LawfulHashable α] (m : ExtHashSet α) (a : α) (fallback : α) : α :=
  m.inner.getKeyD a fallback

/--
Checks if given key is contained and returns the key if it is, otherwise panics.
If no panic occurs the result is guaranteed to be pointer equal to the key in the set.
-/
@[inline] def get! [EquivBEq α] [LawfulHashable α] [Inhabited α] (m : ExtHashSet α) (a : α) : α :=
  m.inner.getKey! a

/--
Returns `true` if the hash set contains no elements.

Note that if your `BEq` instance is not reflexive or your `Hashable` instance is not
lawful, then it is possible that this function returns `false` even though `m.contains a = false`
for all `a`.
-/
@[inline] def isEmpty [EquivBEq α] [LawfulHashable α] (m : ExtHashSet α) : Bool :=
  m.inner.isEmpty

/--
Creates a hash set from a list of elements. Note that unlike repeatedly calling `insert`, if the
collection contains multiple elements that are equal (with regard to `==`), then the last element
in the collection will be present in the returned hash set.
-/
@[inline] def ofList [BEq α] [Hashable α] (l : List α) : ExtHashSet α :=
  ⟨ExtHashMap.unitOfList l⟩

/-- Removes all elements from the hash set for which the given function returns `false`. -/
@[inline] def filter [EquivBEq α] [LawfulHashable α] (f : α → Bool) (m : ExtHashSet α) : ExtHashSet α :=
  ⟨m.inner.filter fun a _ => f a⟩

/--
Inserts multiple mappings into the hash set by iterating over the given collection and calling
`insert`. If the same key appears multiple times, the first occurrence takes precedence.

Note: this precedence behavior is true for `ExtHashSet` and `ExtHashSet.Raw`. The `insertMany` function on
`ExtHashMap`, `DExtHashMap`, `ExtHashMap.Raw` and `DExtHashMap.Raw` behaves differently: it will prefer the last
appearance.
-/
@[inline] def insertMany [EquivBEq α] [LawfulHashable α] {ρ : Type v} [ForIn Id ρ α]
    (m : ExtHashSet α) (l : ρ) : ExtHashSet α :=
  ⟨m.inner.insertManyIfNewUnit l⟩

/--
Computes the union of the given hash sets.

This function always merges the smaller set into the larger set, so the expected runtime is
`O(min(m₁.size, m₂.size))`.
-/
@[inline]
def union [EquivBEq α] [LawfulHashable α] (m₁ m₂ : ExtHashSet α) : ExtHashSet α := ⟨ExtHashMap.union m₁.inner m₂.inner⟩

instance [EquivBEq α] [LawfulHashable α] : Union (ExtHashSet α) := ⟨union⟩

instance [EquivBEq α] [LawfulHashable α] : BEq (ExtHashSet α) where
  beq m₁ m₂ := ExtDHashMap.Const.beq m₁.inner.inner m₂.inner.inner

instance [EquivBEq α] [LawfulHashable α] : ReflBEq (ExtHashSet α) where
  rfl := ExtDHashMap.Const.beq_of_eq _ _ rfl

instance [LawfulBEq α] : LawfulBEq (ExtHashSet α) where
  eq_of_beq {a} {b} hyp := by
    have ⟨⟨_⟩⟩ := a
    have ⟨⟨_⟩⟩ := b
    simp only [mk.injEq, ExtHashMap.mk.injEq] at |- hyp
    exact ExtDHashMap.Const.eq_of_beq _ _ hyp

instance {α : Type u} [BEq α] [LawfulBEq α] [Hashable α] : DecidableEq (ExtHashSet α) :=
  fun _ _ => decidable_of_iff _ beq_iff_eq

/--
Computes the intersection of the given hash sets.

This function always iterates through the smaller set.
-/
@[inline]
def inter [EquivBEq α] [LawfulHashable α] (m₁ m₂ : ExtHashSet α) : ExtHashSet α := ⟨ExtHashMap.inter m₁.inner m₂.inner⟩

instance [EquivBEq α] [LawfulHashable α] : Inter (ExtHashSet α) := ⟨inter⟩

/--
Computes the difference of the given hash sets.

This function always iterates through the smaller set.
-/
@[inline]
def diff [EquivBEq α] [LawfulHashable α] (m₁ m₂ : ExtHashSet α) : ExtHashSet α := ⟨ExtHashMap.diff m₁.inner m₂.inner⟩

instance [EquivBEq α] [LawfulHashable α] : SDiff (ExtHashSet α) := ⟨diff⟩

/--
Creates a hash set from an array of elements. Note that unlike repeatedly calling `insert`, if the
collection contains multiple elements that are equal (with regard to `==`), then the last element
in the collection will be present in the returned hash set.
-/
@[inline] def ofArray [BEq α] [Hashable α] (l : Array α) : ExtHashSet α :=
  ⟨ExtHashMap.unitOfArray l⟩

end ExtHashSet

end Std
