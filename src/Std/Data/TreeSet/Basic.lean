/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.TreeMap.Basic

/-!
# Tree sets

This file develops the type `Std.TreeSet` of tree sets.

Lemmas about the operations on `Std.Data.TreeSet` will be available in the
module `Std.Data.TreeSet.Lemmas`.

See the module `Std.Data.TreeSet.Raw` for a variant of this type which is safe to use in
nested inductive types.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v w w₂

variable {α : Type u} {cmp : α → α → Ordering}

namespace Std

/--
Tree sets.

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

These tree sets contain a bundled well-formedness invariant, which means that they cannot
be used in nested inductive types. For these use cases, `Std.Data.TreeSet.Raw` and
`Std.Data.TreeSet.Raw.WF` unbundle the invariant from the tree set. When in doubt, prefer
`TreeSet` over `TreeSet.Raw`.
-/
structure TreeSet (α : Type u) (cmp : α → α → Ordering := by exact compare) where
  /-- Internal implementation detail of the tree map. -/
  inner : TreeMap α Unit cmp

namespace TreeSet

/--
Creates a new empty tree set. It is also possible and recommended to
use the empty collection notations `∅` and `{}` to create an empty tree set. `simp` replaces
`empty` with `∅`.
-/
@[inline]
def empty : TreeSet α cmp :=
  ⟨TreeMap.empty⟩

instance : EmptyCollection (TreeSet α cmp) where
  emptyCollection := empty

instance : Inhabited (TreeSet α cmp) where
  default := ∅

@[simp]
theorem empty_eq_emptyc : (empty : TreeSet α cmp) = ∅ :=
  rfl

/--
Inserts the given element into the set. If the tree set already contains an element that is
equal (with regard to `cmp`) to the given element, then the tree set is returned unchanged.

Note: this non-replacement behavior is true for `TreeSet` and `TreeSet.Raw`.
The `insert` function on `TreeMap`, `DTreeMap`, `TreeMap.Raw` and `DTreeMap.Raw` behaves
differently: it will overwrite an existing mapping.
-/
@[inline]
def insert (l : TreeSet α cmp) (a : α) : TreeSet α cmp :=
  ⟨l.inner.insertIfNew a ()⟩

instance : Singleton α (TreeSet α cmp) where
  singleton e := (∅ : TreeSet α cmp).insert e

instance : Insert α (TreeSet α cmp) where
  insert e s := s.insert e

instance : LawfulSingleton α (TreeSet α cmp) where
  insert_emptyc_eq _ := rfl

/--
Checks whether an element is present in a set and inserts the element if it was not found.
If the tree set already contains an element that is equal (with regard to `cmp` to the given
element, then the tree set is returned unchanged.

Equivalent to (but potentially faster than) calling `contains` followed by `insert`.
-/
@[inline]
def containsThenInsert (t : TreeSet α cmp) (a : α) : Bool × TreeSet α cmp :=
  letI : Ord α := ⟨cmp⟩
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
def contains (l : TreeSet α cmp) (a : α) : Bool :=
  l.inner.contains a

instance : Membership α (TreeSet α cmp) where
  mem m a := m.contains a

instance {m : TreeSet α cmp} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs <| Decidable (m.contains a)

/-- Returns the number of mappings present in the map. -/
@[inline]
def size (t : TreeSet α cmp) : Nat :=
  t.inner.size

/-- Returns `true` if the tree set contains no mappings. -/
@[inline]
def isEmpty (t : TreeSet α cmp) : Bool :=
  t.inner.isEmpty

/-- Removes the given key if it exists. -/
@[inline]
def erase (t : TreeSet α cmp) (a : α) : TreeSet α cmp :=
  ⟨t.inner.erase a⟩

variable  {γ δ: Type w} {m : Type w → Type w₂} [Monad m]

/-- Removes all elements from the tree set for which the given function returns `false`. -/
@[inline]
def filter (f : α → Bool) (m : TreeSet α cmp) : TreeSet α cmp :=
  ⟨m.inner.filter fun a _ => f a⟩

/--
Monadically computes a value by folding the given function over the elements in the tree set in
ascending order.
-/
@[inline]
def foldlM {m δ} [Monad m] (f : δ → (a : α) → m δ) (init : δ) (t : TreeSet α cmp) : m δ :=
  t.inner.foldlM (fun c a _ => f c a) init

/-- Folds the given function over the elements of the tree set in ascending order. -/
@[inline]
def foldl (f : δ → (a : α) → δ) (init : δ) (t : TreeSet α cmp) : δ :=
  t.inner.foldl (fun c a _ => f c a) init

/-- Carries out a monadic action on each element in the tree set in ascending order. -/
@[inline]
def forM (f : α → m PUnit) (t : TreeSet α cmp) : m PUnit :=
  t.inner.forM (fun a _ => f a)

/--
Support for the `for` loop construct in `do` blocks. The iteration happens in ascending
order.
-/
@[inline]
def forIn (f : α → δ → m (ForInStep δ)) (init : δ) (t : TreeSet α cmp) : m δ :=
  t.inner.forIn (fun a _ c => f a c) init

instance : ForM m (TreeSet α cmp) α where
  forM t f := t.forM f

instance : ForIn m (TreeSet α cmp) α where
  forIn m init f := m.forIn (fun a acc => f a acc) init

/-- Check if all elements satisfy the predicate, short-circuiting if a predicate fails. -/
@[inline]
def any (t : TreeSet α cmp) (p : α → Bool) : Bool :=
  t.inner.any (fun a _ => p a)

/-- Check if any element satisfies the predicate, short-circuiting if a predicate succeeds. -/
@[inline]
def all (t : TreeSet α cmp) (p : α → Bool) : Bool :=
  t.inner.all (fun a _ => p a)

/-- Transforms the tree set into a list of elements in ascending order. -/
@[inline]
def toList (t : TreeSet α cmp) : List α :=
  t.inner.inner.inner.foldr (fun l a _ => a :: l) ∅

/-- Transforms the tree set into an array of elements in ascending order. -/
@[inline]
def toArray (t : TreeSet α cmp) : Array α :=
  t.foldl (init := ∅) fun acc k => acc.push k

/--
Returns a set that contains all mappings of `t₁` and `t₂.

This function ensures that `t₁` is used linearly.
Hence, as long as `t₁` is unshared, the performance characteristics follow the following imperative
description: Iterate over all mappings in `t₂`, inserting them into `t₁`.

Hence, the runtime of this method scales logarithmically in the size of `t₁` and linearly in the
size of `t₂` as long as `t₁` is unshared.
-/
@[inline]
def merge (t₁ t₂ : TreeSet α cmp) : TreeSet α cmp :=
  ⟨TreeMap.mergeWith (fun _ _ _ => ()) t₁.inner t₂.inner⟩

/--
Erases multiple items from the tree set by iterating over the given collection and calling erase.
-/
@[inline]
def eraseMany {ρ} [ForIn Id ρ α] (t : TreeSet α cmp) (l : ρ) : TreeSet α cmp :=
  ⟨t.inner.eraseMany l⟩

instance [Repr α] : Repr (TreeSet α cmp) where
  reprPrec m prec := Repr.addAppParen ("TreeSet.ofList " ++ repr m.toList) prec

end TreeSet

end Std
