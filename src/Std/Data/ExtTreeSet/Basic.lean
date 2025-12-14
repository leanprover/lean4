/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez, Markus Himmel, Paul Reichert
-/
module

prelude
public import Std.Data.ExtTreeMap.Basic

@[expose] public section

/-!
# Extensional tree sets

This file develops the type `Std.ExtTreeSet` of tree sets.

Lemmas about the operations on `Std.Data.ExtTreeSet` will be available in the
module `Std.Data.ExtTreeSet.Lemmas`.

See the module `Std.Data.TreeSet.Raw.Basic` for a variant of this type which is safe to use in
nested inductive types.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v w w₂

variable {α : Type u} {cmp : α → α → Ordering}

namespace Std

/--
Extensional tree sets.

A tree set stores elements of a certain type in a certain order. It depends on a comparator function
that defines an ordering on the keys and provides efficient order-dependent queries, such as
retrieval of the minimum or maximum.

To ensure that the operations behave as expected, the comparator function `cmp` should satisfy
certain laws that ensure a consistent ordering:

* If `a` is less than (or equal) to `b`, then `b` is greater than (or equal) to `a`
and vice versa (see the `OrientedCmp` typeclass).
* If `a` is less than or equal to `b` and `b` is, in turn, less than or equal to `c`, then `a`
is less than or equal to `c` (see the `TransCmp` typeclass).

Keys for which `cmp a b = Ordering.eq` are considered the same, i.e., there can be only one of them
be contained in a single tree set at the same time.

To avoid expensive copies, users should make sure that the tree set is used linearly.

Internally, the tree sets are represented as size-bounded trees, a type of self-balancing binary
search tree with efficient order statistic lookups.

In contrast to regular dependent tree maps, `Std.ExtTreeSet` offers several extensionality lemmas
and therefore has more lemmas about equality of tree sets. This doesn't affect the amount of
supported functions though: `Std.ExtTreeSet` supports all operations from `Std.TreeMap`.

In order to use most functions, a `TransCmp` instance is required. This is necessary to make sure
that the functions are congruent, i.e. equivalent tree sets as parameters produce equivalent return
values.

These tree sets contain a bundled well-formedness invariant, which means that they cannot
be used in nested inductive types. For these use cases, `Std.TreeSet.Raw` and
`Std.TreeSet.Raw.WF` unbundle the invariant from the tree set. When in doubt, prefer
`ExtTreeSet` over `TreeSet.Raw`.
-/
structure ExtTreeSet (α : Type u) (cmp : α → α → Ordering := by exact compare) where
  /-- Internal implementation detail of the tree map. -/
  inner : ExtTreeMap α Unit cmp

namespace ExtTreeSet

/--
Creates a new empty tree set. It is also possible and recommended to
use the empty collection notations `∅` and `{}` to create an empty tree set. `simp` replaces
`empty` with `∅`.
-/
@[inline]
def empty : ExtTreeSet α cmp :=
  ⟨ExtTreeMap.empty⟩

instance : EmptyCollection (ExtTreeSet α cmp) where
  emptyCollection := empty

instance : Inhabited (ExtTreeSet α cmp) where
  default := ∅

@[simp, grind =]
theorem empty_eq_emptyc : (empty : ExtTreeSet α cmp) = ∅ :=
  rfl

/--
Inserts the given element into the set. If the tree set already contains an element that is
equal (with regard to `cmp`) to the given element, then the tree set is returned unchanged.

Note: this non-replacement behavior is true for `ExtTreeSet` and `ExtTreeSet.Raw`.
The `insert` function on `ExtTreeMap`, `ExtDTreeMap`, `ExtTreeMap.Raw` and `ExtDTreeMap.Raw` behaves
differently: it will overwrite an existing mapping.
-/
@[inline]
def insert [TransCmp cmp] (l : ExtTreeSet α cmp) (a : α) : ExtTreeSet α cmp :=
  ⟨l.inner.insertIfNew a ()⟩

instance [TransCmp cmp] : Singleton α (ExtTreeSet α cmp) where
  singleton e := (∅ : ExtTreeSet α cmp).insert e

instance [TransCmp cmp] : Insert α (ExtTreeSet α cmp) where
  insert e s := s.insert e

instance [TransCmp cmp] : LawfulSingleton α (ExtTreeSet α cmp) where
  insert_empty_eq _ := rfl

/--
Checks whether an element is present in a set and inserts the element if it was not found.
If the tree set already contains an element that is equal (with regard to `cmp` to the given
element, then the tree set is returned unchanged.

Equivalent to (but potentially faster than) calling `contains` followed by `insert`.
-/
@[inline]
def containsThenInsert [TransCmp cmp] (t : ExtTreeSet α cmp) (a : α) : Bool × ExtTreeSet α cmp :=
  let p := t.inner.containsThenInsertIfNew a ()
  (p.1, ⟨p.2⟩)

/--
Returns `true` if `a`, or an element equal to `a` according to the comparator `cmp`, is contained
in the set. There is also a `Prop`-valued version of this: `a ∈ t` is equivalent to
`t.contains a = true`.

Observe that this is different behavior than for lists: for lists, `∈` uses `=` and `contains` uses
`==` for equality checks, while for tree sets, both use the given comparator `cmp`.
-/
@[inline]
def contains [TransCmp cmp] (l : ExtTreeSet α cmp) (a : α) : Bool :=
  l.inner.contains a

instance [TransCmp cmp] : Membership α (ExtTreeSet α cmp) where
  mem m a := m.contains a

instance [TransCmp cmp] {m : ExtTreeSet α cmp} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs <| Decidable (m.contains a)

/-- Returns the number of mappings present in the map. -/
@[inline]
def size (t : ExtTreeSet α cmp) : Nat :=
  t.inner.size

/-- Returns `true` if the tree set contains no mappings. -/
@[inline]
def isEmpty (t : ExtTreeSet α cmp) : Bool :=
  t.inner.isEmpty

/-- Removes the given key if it exists. -/
@[inline]
def erase [TransCmp cmp] (t : ExtTreeSet α cmp) (a : α) : ExtTreeSet α cmp :=
  ⟨t.inner.erase a⟩

/--
Checks if given key is contained and returns the key if it is, otherwise `none`.
The result in the `some` case is guaranteed to be pointer equal to the key in the map.
-/
@[inline]
def get? [TransCmp cmp] (t : ExtTreeSet α cmp) (a : α) : Option α :=
  t.inner.getKey? a

/--
Retrieves the key from the set that matches `a`. Ensures that such a key exists by requiring a proof
of `a ∈ m`. The result is guaranteed to be pointer equal to the key in the set.
-/
@[inline]
def get [TransCmp cmp] (t : ExtTreeSet α cmp) (a : α) (h : a ∈ t) : α :=
  t.inner.getKey a h

/--
Checks if given key is contained and returns the key if it is, otherwise panics.
If no panic occurs the result is guaranteed to be pointer equal to the key in the set.
-/
@[inline]
def get! [TransCmp cmp] [Inhabited α] (t : ExtTreeSet α cmp) (a : α) : α :=
  t.inner.getKey! a

/--
Checks if given key is contained and returns the key if it is, otherwise `fallback`.
If they key is contained the result is guaranteed to be pointer equal to the key in the set.
-/
@[inline]
def getD [TransCmp cmp] (t : ExtTreeSet α cmp) (a : α) (fallback : α) : α :=
  t.inner.getKeyD a fallback

/--
Tries to retrieve the smallest element of the tree set, returning `none` if the set is empty.
-/
@[inline]
def min? [TransCmp cmp] (t : ExtTreeSet α cmp) : Option α :=
  ExtTreeMap.minKey? t.inner

/--
Given a proof that the tree set is not empty, retrieves the smallest element.
-/
@[inline]
def min [TransCmp cmp] (t : ExtTreeSet α cmp) (h : t ≠ ∅) : α :=
  ExtTreeMap.minKey t.inner (fun _ => nomatch t)

/--
Tries to retrieve the smallest element of the tree set, panicking if the set is empty.
-/
@[inline]
def min! [TransCmp cmp] [Inhabited α] (t : ExtTreeSet α cmp) : α :=
  ExtTreeMap.minKey! t.inner

/--
Tries to retrieve the smallest element of the tree set, returning `fallback` if the tree set is empty.
-/
@[inline]
def minD [TransCmp cmp] (t : ExtTreeSet α cmp) (fallback : α) : α :=
  ExtTreeMap.minKeyD t.inner fallback

/--
Tries to retrieve the largest element of the tree set, returning `none` if the set is empty.
-/
@[inline]
def max? [TransCmp cmp] (t : ExtTreeSet α cmp) : Option α :=
  ExtTreeMap.maxKey? t.inner

/--
Given a proof that the tree set is not empty, retrieves the largest element.
-/
@[inline]
def max [TransCmp cmp] (t : ExtTreeSet α cmp) (h : t ≠ ∅) : α :=
  ExtTreeMap.maxKey t.inner (fun _ => nomatch t)

/--
Tries to retrieve the largest element of the tree set, panicking if the set is empty.
-/
@[inline]
def max! [TransCmp cmp] [Inhabited α] (t : ExtTreeSet α cmp) : α :=
  ExtTreeMap.maxKey! t.inner

/--
Tries to retrieve the largest element of the tree set, returning `fallback` if the tree set is empty.
-/
@[inline]
def maxD [TransCmp cmp] (t : ExtTreeSet α cmp) (fallback : α) : α :=
  ExtTreeMap.maxKeyD t.inner fallback

/-- Returns the `n`-th smallest element, or `none` if `n` is at least `t.size`. -/
@[inline]
def atIdx? [TransCmp cmp] (t : ExtTreeSet α cmp) (n : Nat) : Option α :=
  ExtTreeMap.keyAtIdx? t.inner n

/-- Returns the `n`-th smallest element. -/
@[inline]
def atIdx [TransCmp cmp] (t : ExtTreeSet α cmp) (n : Nat) (h : n < t.size) : α :=
  ExtTreeMap.keyAtIdx t.inner n h

/-- Returns the `n`-th smallest element, or panics if `n` is at least `t.size`. -/
@[inline]
def atIdx! [TransCmp cmp] [Inhabited α] (t : ExtTreeSet α cmp) (n : Nat) : α :=
  ExtTreeMap.keyAtIdx! t.inner n

/-- Returns the `n`-th smallest element, or `fallback` if `n` is at least `t.size`. -/
@[inline]
def atIdxD [TransCmp cmp] (t : ExtTreeSet α cmp) (n : Nat) (fallback : α) : α :=
  ExtTreeMap.keyAtIdxD t.inner n fallback

/--
Tries to retrieve the smallest element that is greater than or equal to the
given element, returning `none` if no such element exists.
-/
@[inline]
def getGE? [TransCmp cmp] (t : ExtTreeSet α cmp) (k : α) : Option α :=
  ExtTreeMap.getKeyGE? t.inner k

/--
Tries to retrieve the smallest element that is greater than the given element,
returning `none` if no such element exists.
-/
@[inline]
def getGT? [TransCmp cmp] (t : ExtTreeSet α cmp) (k : α) : Option α :=
  ExtTreeMap.getKeyGT? t.inner k

/--
Tries to retrieve the largest element that is less than or equal to the
given element, returning `none` if no such element exists.
-/
@[inline]
def getLE? [TransCmp cmp] (t : ExtTreeSet α cmp) (k : α) : Option α :=
  ExtTreeMap.getKeyLE? t.inner k

/--
Tries to retrieve the smallest element that is less than the given element,
returning `none` if no such element exists.
-/
@[inline]
def getLT? [TransCmp cmp] (t : ExtTreeSet α cmp) (k : α) : Option α :=
  ExtTreeMap.getKeyLT? t.inner k

/--
Given a proof that such an element exists, retrieves the smallest element that is
greater than or equal to the given element.
-/
@[inline]
def getGE [TransCmp cmp] (t : ExtTreeSet α cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isGE) : α :=
  ExtTreeMap.getKeyGE t.inner k h

/--
Given a proof that such an element exists, retrieves the smallest element that is
greater than the given element.
-/
@[inline]
def getGT [TransCmp cmp] (t : ExtTreeSet α cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .gt) : α :=
  ExtTreeMap.getKeyGT t.inner k h

/--
Given a proof that such an element exists, retrieves the largest element that is
less than or equal to the given element.
-/
@[inline]
def getLE [TransCmp cmp] (t : ExtTreeSet α cmp) (k : α) (h : ∃ a ∈ t, (cmp a k).isLE) : α :=
  ExtTreeMap.getKeyLE t.inner k h

/--
Given a proof that such an element exists, retrieves the smallest element that is
less than the given element.
-/
@[inline]
def getLT [TransCmp cmp] (t : ExtTreeSet α cmp) (k : α) (h : ∃ a ∈ t, cmp a k = .lt) : α :=
  ExtTreeMap.getKeyLT t.inner k h

/--
Tries to retrieve the smallest element that is greater than or equal to the
given element, panicking if no such element exists.
-/
@[inline]
def getGE! [TransCmp cmp] [Inhabited α] (t : ExtTreeSet α cmp) (k : α) : α :=
  ExtTreeMap.getKeyGE! t.inner k

/--
Tries to retrieve the smallest element that is greater than the given element,
panicking if no such element exists.
-/
@[inline]
def getGT! [TransCmp cmp] [Inhabited α] (t : ExtTreeSet α cmp) (k : α) : α :=
  ExtTreeMap.getKeyGT! t.inner k

/--
Tries to retrieve the largest element that is less than or equal to the
given element, panicking if no such element exists.
-/
@[inline]
def getLE! [TransCmp cmp] [Inhabited α] (t : ExtTreeSet α cmp) (k : α) : α :=
  ExtTreeMap.getKeyLE! t.inner k

/--
Tries to retrieve the smallest element that is less than the given element,
panicking if no such element exists.
-/
@[inline]
def getLT! [TransCmp cmp] [Inhabited α] (t : ExtTreeSet α cmp) (k : α) : α :=
  ExtTreeMap.getKeyLT! t.inner k

/--
Tries to retrieve the smallest element that is greater than or equal to the
given element, returning `fallback` if no such element exists.
-/
@[inline]
def getGED [TransCmp cmp] (t : ExtTreeSet α cmp) (k : α) (fallback : α) : α :=
  ExtTreeMap.getKeyGED t.inner k fallback

/--
Tries to retrieve the smallest element that is greater than the given element,
returning `fallback` if no such element exists.
-/
@[inline]
def getGTD [TransCmp cmp] (t : ExtTreeSet α cmp) (k : α) (fallback : α) : α :=
  ExtTreeMap.getKeyGTD t.inner k fallback

/--
Tries to retrieve the largest element that is less than or equal to the
given element, returning `fallback` if no such element exists.
-/
@[inline]
def getLED [TransCmp cmp] (t : ExtTreeSet α cmp) (k : α) (fallback : α) : α :=
  ExtTreeMap.getKeyLED t.inner k fallback

/--
Tries to retrieve the smallest element that is less than the given element,
returning `fallback` if no such element exists.
-/
@[inline]
def getLTD [TransCmp cmp] (t : ExtTreeSet α cmp) (k : α) (fallback : α) : α :=
  ExtTreeMap.getKeyLTD t.inner k fallback

variable {γ δ : Type w} {m : Type w → Type w₂} [Monad m] [LawfulMonad m]

/-- Removes all elements from the tree set for which the given function returns `false`. -/
@[inline]
def filter (f : α → Bool) (m : ExtTreeSet α cmp) : ExtTreeSet α cmp :=
  ⟨m.inner.filter fun a _ => f a⟩

/--
Monadically computes a value by folding the given function over the elements in the tree set in
ascending order.
-/
@[inline]
def foldlM [TransCmp cmp] (f : δ → (a : α) → m δ) (init : δ) (t : ExtTreeSet α cmp) : m δ :=
  t.inner.foldlM (fun c a _ => f c a) init

/-- Folds the given function over the elements of the tree set in ascending order. -/
@[inline]
def foldl [TransCmp cmp] (f : δ → (a : α) → δ) (init : δ) (t : ExtTreeSet α cmp) : δ :=
  t.inner.foldl (fun c a _ => f c a) init

/--
Monadically computes a value by folding the given function over the elements in the tree set in
descending order.
-/
@[inline]
def foldrM [TransCmp cmp] (f : (a : α) → δ → m δ) (init : δ) (t : ExtTreeSet α cmp) : m δ :=
  t.inner.foldrM (fun a _ acc => f a acc) init

/-- Folds the given function over the elements of the tree set in descending order. -/
@[inline]
def foldr [TransCmp cmp] (f : (a : α) → δ → δ) (init : δ) (t : ExtTreeSet α cmp) : δ :=
  t.inner.foldr (fun a _ acc => f a acc) init

/-- Partitions a tree set into two tree sets based on a predicate. -/
@[inline]
def partition [TransCmp cmp] (f : (a : α) → Bool) (t : ExtTreeSet α cmp) :
    ExtTreeSet α cmp × ExtTreeSet α cmp :=
  let p := t.inner.partition fun a _ => f a; (⟨p.1⟩, ⟨p.2⟩)

/-- Carries out a monadic action on each element in the tree set in ascending order. -/
@[inline]
def forM [TransCmp cmp] (f : α → m PUnit) (t : ExtTreeSet α cmp) : m PUnit :=
  t.inner.forM (fun a _ => f a)

/--
Support for the `for` loop construct in `do` blocks. The iteration happens in ascending
order.
-/
@[inline]
def forIn [TransCmp cmp] (f : α → δ → m (ForInStep δ)) (init : δ) (t : ExtTreeSet α cmp) : m δ :=
  t.inner.forIn (fun a _ c => f a c) init


instance [TransCmp cmp] [Monad m] [LawfulMonad m] : ForM m (ExtTreeSet α cmp) α where
  forM t f := forM f t

instance [TransCmp cmp] [Monad m] [LawfulMonad m] : ForIn m (ExtTreeSet α cmp) α where
  forIn m init f := forIn f init m

/-- Check if all elements satisfy the predicate, short-circuiting if a predicate fails. -/
@[inline]
def any [TransCmp cmp] (t : ExtTreeSet α cmp) (p : α → Bool) : Bool :=
  t.inner.any (fun a _ => p a)

/-- Check if any element satisfies the predicate, short-circuiting if a predicate succeeds. -/
@[inline]
def all [TransCmp cmp] (t : ExtTreeSet α cmp) (p : α → Bool) : Bool :=
  t.inner.all (fun a _ => p a)

/-- Transforms the tree set into a list of elements in ascending order. -/
@[inline]
def toList [TransCmp cmp] (t : ExtTreeSet α cmp) : List α :=
  t.inner.keys

/-- Transforms a list into a tree set. -/
def ofList (l : List α) (cmp : α → α → Ordering := by exact compare) : ExtTreeSet α cmp :=
  ⟨ExtTreeMap.unitOfList l cmp⟩

/-- Transforms the tree set into an array of elements in ascending order. -/
@[inline]
def toArray [TransCmp cmp] (t : ExtTreeSet α cmp) : Array α :=
  t.inner.keysArray

/-- Transforms an array into a tree set. -/
def ofArray (a : Array α) (cmp : α → α → Ordering := by exact compare) : ExtTreeSet α cmp :=
  ⟨ExtTreeMap.unitOfArray a cmp⟩

/--
Returns a set that contains all mappings of `t₁` and `t₂.

This function ensures that `t₁` is used linearly.
Hence, as long as `t₁` is unshared, the performance characteristics follow the following imperative
description: Iterate over all mappings in `t₂`, inserting them into `t₁`.

Hence, the runtime of this method scales logarithmically in the size of `t₁` and linearly in the
size of `t₂` as long as `t₁` is unshared.
-/
@[inline]
def merge [TransCmp cmp] (t₁ t₂ : ExtTreeSet α cmp) : ExtTreeSet α cmp :=
  ⟨ExtTreeMap.mergeWith (fun _ _ _ => ()) t₁.inner t₂.inner⟩

/--
Inserts multiple elements into the tree set by iterating over the given collection and calling
`insert`. If the same element (with respect to `cmp`) appears multiple times, the first occurrence
takes precedence.

Note: this precedence behavior is true for `ExtTreeSet` and `ExtTreeSet.Raw`. The `insertMany` function on
`ExtTreeMap`, `ExtDTreeMap`, `ExtTreeMap.Raw` and `ExtDTreeMap.Raw` behaves differently: it will prefer the last
appearance.
-/
@[inline]
def insertMany [TransCmp cmp] {ρ} [ForIn Id ρ α] (t : ExtTreeSet α cmp) (l : ρ) : ExtTreeSet α cmp :=
  ⟨ExtTreeMap.insertManyIfNewUnit t.inner l⟩

/--
Computes the union of the given tree sets. If both maps contain elements that are equal according
to the comparison function, the element contained in the second argument will appear in the result.

This function always merges the smaller set into the larger set.
-/
@[inline]
def union [TransCmp cmp] (t₁ t₂ : ExtTreeSet α cmp) : ExtTreeSet α cmp := ⟨ExtTreeMap.union t₁.inner t₂.inner⟩

instance [TransCmp cmp] : Union (ExtTreeSet α cmp) := ⟨union⟩

/--
Computes the intersection of the given tree sets.

This function always iterates through the smaller set.
-/
@[inline]
def inter [TransCmp cmp] (t₁ t₂ : ExtTreeSet α cmp) : ExtTreeSet α cmp := ⟨ExtTreeMap.inter t₁.inner t₂.inner⟩

instance [TransCmp cmp] : Inter (ExtTreeSet α cmp) := ⟨inter⟩

instance [TransCmp cmp] : BEq (ExtTreeSet α cmp) where
  beq m₁ m₂ := ExtDTreeMap.Const.beq m₁.inner.inner m₂.inner.inner

instance [TransCmp cmp] : ReflBEq (ExtTreeSet α cmp) where
  rfl := ExtDTreeMap.Const.beq_of_eq _ _ rfl

instance [TransCmp cmp] [LawfulEqCmp cmp] : LawfulBEq (ExtTreeSet α cmp) where
  eq_of_beq {a} {b} hyp := by
    have ⟨⟨_⟩⟩ := a
    have ⟨⟨_⟩⟩ := b
    simp only [mk.injEq, ExtTreeMap.mk.injEq] at |- hyp
    exact ExtDTreeMap.Const.eq_of_beq _ _ hyp

/--
Computes the difference of the given tree sets.

This function always iterates through the smaller set.
-/
@[inline]
def diff [TransCmp cmp] (t₁ t₂ : ExtTreeSet α cmp) : ExtTreeSet α cmp := ⟨ExtTreeMap.diff t₁.inner t₂.inner⟩

instance [TransCmp cmp] : SDiff (ExtTreeSet α cmp) := ⟨diff⟩

instance {α : Type u} {cmp : α → α → Ordering} [LawfulEqCmp cmp] [TransCmp cmp] : DecidableEq (ExtTreeSet α cmp) :=
  fun _ _ => decidable_of_iff _ beq_iff_eq

/--
Erases multiple items from the tree set by iterating over the given collection and calling erase.
-/
@[inline]
def eraseMany [TransCmp cmp] {ρ} [ForIn Id ρ α] (t : ExtTreeSet α cmp) (l : ρ) : ExtTreeSet α cmp :=
  ⟨t.inner.eraseMany l⟩

instance [TransCmp cmp] [Repr α] : Repr (ExtTreeSet α cmp) where
  reprPrec m prec := Repr.addAppParen ("Std.ExtTreeSet.ofList " ++ repr m.toList) prec

end ExtTreeSet

end Std
