/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.HashMap.Raw

/-
# Hash sets with unbundled well-formedness invariant

This module develops the type `Std.Data.HashSet.Raw` of dependent hash
set with unbundled well-formedness invariant.

This version is safe to use in nested inductive types. The well-formedness predicate is
available as `Std.Data.HashSet.Raw.WF` and we prove in this file that all operations preserve
well-formedness. When in doubt, prefer `HashSet` over `HashSet.Raw`.

Lemmas about the operations on `Std.Data.HashSet.Raw` are available in the module
`Std.Data.HashSet.RawLemmas`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v

variable {α : Type u}

namespace Std

namespace HashSet

/--
Hash sets without a bundled well-formedness invariant, suitable for use in nested
inductive types. The well-formedness invariant is called `Raw.WF`. When in doubt, prefer `HashSet`
over `HashSet.Raw`. Lemmas about the operations on `Std.Data.HashSet.Raw` are available in the
module `Std.Data.HashSet.RawLemmas`.

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
-/
structure Raw (α : Type u) where
  /-- Internal implementation detail of the hash set. -/
  inner : HashMap.Raw α Unit

namespace Raw

/--
Creates a new empty hash set. The optional parameter `capacity` can be supplied to presize the set
so that it can hold the given number of elements without reallocating. It is also possible to use
the empty collection notations `∅` and `{}` to create an empty hash set with the default capacity.
-/
@[inline] def empty (capacity := 8) : Raw α :=
  ⟨HashMap.Raw.empty capacity⟩

instance : EmptyCollection (Raw α) where
  emptyCollection := empty

instance : Inhabited (Raw α) where
  default := ∅

/--
Inserts the given element into the set. If the hash set already contains an element that is
equal (with regard to `==`) to the given element, then the hash set is returned unchanged.
-/
@[inline] def insert [BEq α] [Hashable α] (m : Raw α) (a : α) : Raw α :=
  ⟨m.inner.insertIfNew a ()⟩

instance [BEq α] [Hashable α] : Singleton α (Raw α) := ⟨fun a => Raw.empty.insert a⟩

instance [BEq α] [Hashable α] : Insert α (Raw α) := ⟨fun a s => s.insert a⟩

instance [BEq α] [Hashable α] : LawfulSingleton α (Raw α) := ⟨fun _ => rfl⟩

/--
Checks whether an element is present in a set and inserts the element if it was not found.
If the hash set already contains an element that is equal (with regard to `==`) to the given
element, then the hash set is returned unchanged.

Equivalent to (but potentially faster than) calling `contains` followed by `insert`.
-/
@[inline] def containsThenInsert [BEq α] [Hashable α] (m : Raw α) (a : α) : Bool × Raw α :=
  let ⟨replaced, r⟩ := m.inner.containsThenInsertIfNew a ()
  ⟨replaced, ⟨r⟩⟩

/--
Returns `true` if the given element is present in the set. There is also a `Prop`-valued version
of this: `a ∈ m` is equivalent to `m.contains a = true`.

Observe that this is different behavior than for lists: for lists, `∈` uses `=` and `contains` use
`==` for comparisons, while for hash sets, both use `==`.
-/
@[inline] def contains [BEq α] [Hashable α] (m : Raw α) (a : α) : Bool :=
  m.inner.contains a

instance [BEq α] [Hashable α] : Membership α (Raw α) where
  mem m a := a ∈ m.inner

instance [BEq α] [Hashable α] {m : Raw α} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs (Decidable (a ∈ m.inner))

/-- Removes the element if it exists. -/
@[inline] def erase [BEq α] [Hashable α] (m : Raw α) (a : α) : Raw α :=
  ⟨m.inner.erase a⟩

/-- The number of elements present in the set -/
@[inline] def size (m : Raw α) : Nat :=
  m.inner.size

/--
Checks if given key is contained and returns the key if it is, otherwise `none`.
The result in the `some` case is guaranteed to be pointer equal to the key in the map.
-/
@[inline] def get? [BEq α] [Hashable α] (m : Raw α) (a : α) : Option α :=
  m.inner.getKey? a

/--
Retrieves the key from the set that matches `a`. Ensures that such a key exists by requiring a proof
of `a ∈ m`. The result is guaranteed to be pointer equal to the key in the set.
-/
@[inline] def get [BEq α] [Hashable α] (m : Raw α) (a : α) (h : a ∈ m) : α :=
  m.inner.getKey a h

/--
Checks if given key is contained and returns the key if it is, otherwise `fallback`.
If they key is contained the result is guaranteed to be pointer equal to the key in the set.
-/
@[inline] def getD [BEq α] [Hashable α] (m : Raw α) (a : α) (fallback : α) : α :=
  m.inner.getKeyD a fallback

/--
Checks if given key is contained and returns the key if it is, otherwise panics.
If no panic occurs the result is guaranteed to be pointer equal to the key in the set.
-/
@[inline] def get! [BEq α] [Hashable α] [Inhabited α] (m : Raw α) (a : α) : α :=
  m.inner.getKey! a

/--
Returns `true` if the hash set contains no elements.

Note that if your `BEq` instance is not reflexive or your `Hashable` instance is not
lawful, then it is possible that this function returns `false` even though `m.contains a = false`
for all `a`.
-/
@[inline] def isEmpty (m : Raw α) : Bool :=
  m.inner.isEmpty

/-- Transforms the hash set into a list of elements in some order. -/
@[inline] def toList (m : Raw α) : List α :=
  m.inner.keys

section Unverified

/-! We currently do not provide lemmas for the functions below. -/

/-! We currently do not provide lemmas for the functions below. -/

/-- Removes all elements from the hash set for which the given function returns `false`. -/
@[inline] def filter [BEq α] [Hashable α] (f : α → Bool) (m : Raw α) : Raw α :=
  ⟨m.inner.filter fun a _ => f a⟩

/--
Monadically computes a value by folding the given function over the elements in the hash set in some
order.
-/
@[inline] def foldM {m : Type v → Type v} [Monad m] {β : Type v} (f : β → α → m β) (init : β)
    (b : Raw α) : m β :=
  b.inner.foldM (fun b a _ => f b a) init

/-- Folds the given function over the elements of the hash set in some order. -/
@[inline] def fold {β : Type v} (f : β → α → β) (init : β) (m : Raw α) : β :=
  m.inner.fold (fun b a _ => f b a) init

/-- Carries out a monadic action on each element in the hash set in some order. -/
@[inline] def forM {m : Type v → Type v} [Monad m] (f : α → m PUnit) (b : Raw α) : m PUnit :=
  b.inner.forM (fun a _ => f a)

/-- Support for the `for` loop construct in `do` blocks. -/
@[inline] def forIn {m : Type v → Type v} [Monad m] {β : Type v} (f : α → β → m (ForInStep β))
    (init : β) (b : Raw α) : m β :=
  b.inner.forIn (fun a _ acc => f a acc) init

instance {m : Type v → Type v} : ForM m (Raw α) α where
  forM m f := m.forM f

instance {m : Type v → Type v} : ForIn m (Raw α) α where
  forIn m init f := m.forIn f init

/-- Check if all elements satisfy the predicate, short-circuiting if a predicate fails. -/
@[inline] def all (m : Raw α) (p : α → Bool) : Bool := Id.run do
  for a in m do
    if ¬ p a then return false
  return true

/-- Check if any element satisfies the predicate, short-circuiting if a predicate succeeds. -/
@[inline] def any (m : Raw α) (p : α → Bool) : Bool := Id.run do
  for a in m do
    if p a then return true
  return false


/-- Transforms the hash set into an array of elements in some order. -/
@[inline] def toArray (m : Raw α) : Array α :=
  m.inner.keysArray

/--
Inserts multiple elements into the hash set. Note that unlike repeatedly calling `insert`, if the
collection contains multiple elements that are equal (with regard to `==`), then the last element
in the collection will be present in the returned hash set.
-/
@[inline] def insertMany [BEq α] [Hashable α] {ρ : Type v} [ForIn Id ρ α] (m : Raw α) (l : ρ) :
    Raw α :=
  ⟨m.inner.insertManyUnit l⟩

/--
Creates a hash set from a list of elements. Note that unlike repeatedly calling `insert`, if the
collection contains multiple elements that are equal (with regard to `==`), then the last element
in the collection will be present in the returned hash set.
-/
@[inline] def ofList [BEq α] [Hashable α] (l : List α) : Raw α :=
  ⟨HashMap.Raw.unitOfList l⟩

/--
Creates a hash set from an array of elements. Note that unlike repeatedly calling `insert`, if the
collection contains multiple elements that are equal (with regard to `==`), then the last element
in the collection will be present in the returned hash set.
-/
@[inline] def ofArray [BEq α] [Hashable α] (l : Array α) : Raw α :=
  ⟨HashMap.Raw.unitOfArray l⟩

/-- Computes the union of the given hash sets, by traversing `m₂` and inserting its elements into `m₁`. -/
@[inline] def union [BEq α] [Hashable α] (m₁ m₂ : Raw α) : Raw α :=
  m₂.fold (init := m₁) fun acc x => acc.insert x

instance [BEq α] [Hashable α] : Union (Raw α) := ⟨union⟩

/--
Returns the number of buckets in the internal representation of the hash set. This function may
be useful for things like monitoring system health, but it should be considered an internal
implementation detail.
-/
def Internal.numBuckets (m : Raw α) : Nat :=
  HashMap.Raw.Internal.numBuckets m.inner

instance [Repr α] : Repr (Raw α) where
  reprPrec m prec := Repr.addAppParen ("Std.HashSet.Raw.ofList " ++ reprArg m.toList) prec

end Unverified

/--
Well-formedness predicate for hash sets. Users of `HashSet` will not need to interact with this.
Users of `HashSet.Raw` will need to provide proofs of `WF` to lemmas and should use lemmas like
`WF.empty` and `WF.insert` (which are always named exactly like the operations they are about) to
show that set operations preserve well-formedness.
-/
structure WF [BEq α] [Hashable α] (m : Raw α) : Prop where
  /-- Internal implementation detail of the hash set -/
  out : m.inner.WF

theorem WF.empty [BEq α] [Hashable α] {c} : (empty c : Raw α).WF :=
  ⟨HashMap.Raw.WF.empty⟩

theorem WF.emptyc [BEq α] [Hashable α] : (∅ : Raw α).WF :=
  ⟨HashMap.Raw.WF.empty⟩

theorem WF.insert [BEq α] [Hashable α] {m : Raw α} {a : α} (h : m.WF) : (m.insert a).WF :=
  ⟨HashMap.Raw.WF.insertIfNew h.out⟩

theorem WF.containsThenInsert [BEq α] [Hashable α] {m : Raw α} {a : α} (h : m.WF) :
    (m.containsThenInsert a).2.WF :=
  ⟨HashMap.Raw.WF.containsThenInsertIfNew h.out⟩

theorem WF.erase [BEq α] [Hashable α] {m : Raw α} {a : α} (h : m.WF) : (m.erase a).WF :=
  ⟨HashMap.Raw.WF.erase h.out⟩

theorem WF.filter [BEq α] [Hashable α] {m : Raw α} {f : α → Bool} (h : m.WF) : (m.filter f).WF :=
  ⟨HashMap.Raw.WF.filter h.out⟩

theorem WF.insertMany [BEq α] [Hashable α] {ρ : Type v} [ForIn Id ρ α] {m : Raw α} {l : ρ}
    (h : m.WF) : (m.insertMany l).WF :=
  ⟨HashMap.Raw.WF.insertManyUnit h.out⟩

theorem WF.ofList [BEq α] [Hashable α] {l : List α} :
    (ofList l : Raw α).WF :=
  ⟨HashMap.Raw.WF.unitOfList⟩

end Raw

end HashSet

end Std
