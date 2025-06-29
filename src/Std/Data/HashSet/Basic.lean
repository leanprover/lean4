/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Std.Data.HashMap.Basic

public @[expose] section

/-!
# Hash sets

This module develops the type `Std.HashSet` of hash sets.

Lemmas about the operations on `Std.HashSet` are available in the
module `Std.Data.HashSet.Lemmas`.

See the module `Std.Data.HashSet.Raw` for a variant of this type which is safe to use in
nested inductive types.
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

These hash sets contain a bundled well-formedness invariant, which means that they cannot
be used in nested inductive types. For these use cases, `Std.Data.HashSet.Raw` and
`Std.Data.HashSet.Raw.WF` unbundle the invariant from the hash set. When in doubt, prefer
`HashSet` over `HashSet.Raw`.
-/
structure HashSet (α : Type u) [BEq α] [Hashable α] where
  /-- Internal implementation detail of the hash set. -/
  inner : HashMap α Unit

namespace HashSet

/--
Creates a new empty hash set. The optional parameter `capacity` can be supplied to presize the
set so that it can hold the given number of elements without reallocating. It is also possible to
use the empty collection notations `∅` and `{}` to create an empty hash set with the default
capacity.
-/
@[inline] def emptyWithCapacity [BEq α] [Hashable α] (capacity := 8) : HashSet α :=
  ⟨HashMap.emptyWithCapacity capacity⟩

@[deprecated emptyWithCapacity (since := "2025-03-12"), inherit_doc emptyWithCapacity]
abbrev empty := @emptyWithCapacity

instance [BEq α] [Hashable α] : EmptyCollection (HashSet α) where
  emptyCollection := emptyWithCapacity

instance [BEq α] [Hashable α] : Inhabited (HashSet α) where
  default := ∅

/--
Two hash sets are equivalent in the sense of `Equiv` iff all their values are equal.
-/
structure Equiv (m₁ m₂ : HashSet α) where
  /-- Internal implementation detail of the hash map -/
  inner : m₁.1.Equiv m₂.1

@[inherit_doc] scoped infixl:50 " ~m " => Equiv

/--
Inserts the given element into the set. If the hash set already contains an element that is
equal (with regard to `==`) to the given element, then the hash set is returned unchanged.

Note: this non-replacement behavior is true for `HashSet` and `HashSet.Raw`.
The `insert` function on `HashMap`, `DHashMap`, `HashMap.Raw` and `DHashMap.Raw` behaves
differently: it will overwrite an existing mapping.
-/
@[inline] def insert (m : HashSet α) (a : α) : HashSet α :=
  ⟨m.inner.insertIfNew a ()⟩

instance : Singleton α (HashSet α) := ⟨fun a => (∅ : HashSet α).insert a⟩

instance : Insert α (HashSet α) := ⟨fun a s => s.insert a⟩

/--
Checks whether an element is present in a set and inserts the element if it was not found.
If the hash set already contains an element that is equal (with regard to `==`) to the given
element, then the hash set is returned unchanged.

Equivalent to (but potentially faster than) calling `contains` followed by `insert`.
-/
@[inline] def containsThenInsert (m : HashSet α) (a : α) : Bool × HashSet α :=
  let ⟨replaced, r⟩ := m.inner.containsThenInsertIfNew a ()
  ⟨replaced, ⟨r⟩⟩

/--
Returns `true` if the given key is present in the set. There is also a `Prop`-valued version of
this: `a ∈ m` is equivalent to `m.contains a = true`.

Observe that this is different behavior than for lists: for lists, `∈` uses `=` and `contains` use
`==` for comparisons, while for hash sets, both use `==`.
-/
@[inline] def contains (m : HashSet α) (a : α) : Bool :=
  m.inner.contains a

instance [BEq α] [Hashable α] : Membership α (HashSet α) where
  mem m a := a ∈ m.inner

instance [BEq α] [Hashable α] {m : HashSet α} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.inner))

/-- Removes the element if it exists. -/
@[inline] def erase (m : HashSet α) (a : α) : HashSet α :=
  ⟨m.inner.erase a⟩

/-- The number of elements present in the set -/
@[inline] def size (m : HashSet α) : Nat :=
  m.inner.size

/--
Checks if given key is contained and returns the key if it is, otherwise `none`.
The result in the `some` case is guaranteed to be pointer equal to the key in the set.
-/
@[inline] def get? (m : HashSet α) (a : α) : Option α :=
  m.inner.getKey? a

/--
Retrieves the key from the set that matches `a`. Ensures that such a key exists by requiring a proof
of `a ∈ m`. The result is guaranteed to be pointer equal to the key in the set.
-/
@[inline] def get [BEq α] [Hashable α] (m : HashSet α) (a : α) (h : a ∈ m) : α :=
  m.inner.getKey a h

/--
Checks if given key is contained and returns the key if it is, otherwise `fallback`.
If they key is contained the result is guaranteed to be pointer equal to the key in the set.
-/
@[inline] def getD [BEq α] [Hashable α] (m : HashSet α) (a : α) (fallback : α) : α :=
  m.inner.getKeyD a fallback

/--
Checks if given key is contained and returns the key if it is, otherwise panics.
If no panic occurs the result is guaranteed to be pointer equal to the key in the set.
-/
@[inline] def get! [BEq α] [Hashable α] [Inhabited α] (m : HashSet α) (a : α) : α :=
  m.inner.getKey! a

/--
Returns `true` if the hash set contains no elements.

Note that if your `BEq` instance is not reflexive or your `Hashable` instance is not
lawful, then it is possible that this function returns `false` even though `m.contains a = false`
for all `a`.
-/
@[inline] def isEmpty (m : HashSet α) : Bool :=
  m.inner.isEmpty

/-- Transforms the hash set into a list of elements in some order. -/
@[inline] def toList (m : HashSet α) : List α :=
  m.inner.keys

/--
Creates a hash set from a list of elements. Note that unlike repeatedly calling `insert`, if the
collection contains multiple elements that are equal (with regard to `==`), then the last element
in the collection will be present in the returned hash set.
-/
@[inline] def ofList [BEq α] [Hashable α] (l : List α) : HashSet α :=
  ⟨HashMap.unitOfList l⟩

/--
Monadically computes a value by folding the given function over the elements in the hash set in some
order.
-/
@[inline] def foldM {m : Type v → Type v} [Monad m] {β : Type v}
    (f : β → α → m β) (init : β) (b : HashSet α) : m β :=
  b.inner.foldM (fun b a _ => f b a) init

/-- Folds the given function over the elements of the hash set in some order. -/
@[inline] def fold {β : Type v} (f : β → α → β) (init : β) (m : HashSet α) :
    β :=
  m.inner.fold (fun b a _ => f b a) init

/-- Carries out a monadic action on each element in the hash set in some order. -/
@[inline] def forM {m : Type v → Type v} [Monad m] (f : α → m PUnit)
    (b : HashSet α) : m PUnit :=
  b.inner.forM (fun a _ => f a)

/-- Support for the `for` loop construct in `do` blocks. -/
@[inline] def forIn {m : Type v → Type v} [Monad m] {β : Type v}
    (f : α → β → m (ForInStep β)) (init : β) (b : HashSet α) : m β :=
  b.inner.forIn (fun a _ acc => f a acc) init

instance [BEq α] [Hashable α] {m : Type v → Type v} : ForM m (HashSet α) α where
  forM m f := m.forM f

instance [BEq α] [Hashable α] {m : Type v → Type v} : ForIn m (HashSet α) α where
  forIn m init f := m.forIn f init

/-- Removes all elements from the hash set for which the given function returns `false`. -/
@[inline] def filter (f : α → Bool) (m : HashSet α) : HashSet α :=
  ⟨m.inner.filter fun a _ => f a⟩

/--
Inserts multiple mappings into the hash set by iterating over the given collection and calling
`insert`. If the same key appears multiple times, the first occurrence takes precedence.

Note: this precedence behavior is true for `HashSet` and `HashSet.Raw`. The `insertMany` function on
`HashMap`, `DHashMap`, `HashMap.Raw` and `DHashMap.Raw` behaves differently: it will prefer the last
appearance.
-/
@[inline] def insertMany {ρ : Type v} [ForIn Id ρ α] (m : HashSet α) (l : ρ) :
    HashSet α :=
  ⟨m.inner.insertManyIfNewUnit l⟩

section Unverified

/-! We currently do not provide lemmas for the functions below. -/

/-- Partition a hashset into two hashsets based on a predicate. -/
@[inline] def partition (f : α → Bool) (m : HashSet α) : HashSet α × HashSet α :=
  let ⟨l, r⟩ := m.inner.partition fun a _ => f a
  ⟨⟨l⟩, ⟨r⟩⟩

/-- Check if all elements satisfy the predicate, short-circuiting if a predicate fails. -/
@[inline] def all (m : HashSet α) (p : α → Bool) : Bool := Id.run do
  for a in m do
    if ¬ p a then return false
  return true

/-- Check if any element satisfies the predicate, short-circuiting if a predicate succeeds. -/
@[inline] def any (m : HashSet α) (p : α → Bool) : Bool := Id.run do
  for a in m do
    if p a then return true
  return false


/-- Transforms the hash set into an array of elements in some order. -/
@[inline] def toArray (m : HashSet α) : Array α :=
  m.inner.keysArray

/--
Creates a hash set from an array of elements. Note that unlike repeatedly calling `insert`, if the
collection contains multiple elements that are equal (with regard to `==`), then the last element
in the collection will be present in the returned hash set.
-/
@[inline] def ofArray [BEq α] [Hashable α] (l : Array α) : HashSet α :=
  ⟨HashMap.unitOfArray l⟩

/-- Computes the union of the given hash sets, by traversing `m₂` and inserting its elements into `m₁`. -/
@[inline] def union [BEq α] [Hashable α] (m₁ m₂ : HashSet α) : HashSet α :=
  m₂.fold (init := m₁) fun acc x => acc.insert x

instance [BEq α] [Hashable α] : Union (HashSet α) := ⟨union⟩

/--
Returns the number of buckets in the internal representation of the hash set. This function may
be useful for things like monitoring system health, but it should be considered an internal
implementation detail.
-/
def Internal.numBuckets (m : HashSet α) : Nat :=
  HashMap.Internal.numBuckets m.inner

instance [BEq α] [Hashable α] [Repr α] : Repr (HashSet α) where
  reprPrec m prec := Repr.addAppParen ("Std.HashSet.ofList " ++ reprArg m.toList) prec

end Unverified

end HashSet

end Std
