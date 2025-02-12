/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.DTreeMap.Internal.WF.Def

/-!
# Dependent tree maps

This file develops the type `Std.DTreeMap` of dependent tree maps.

Lemmas about the operations on `Std.DTreeMap` will be available in the
module `Std.Data.DTreeMap.Lemmas`.

See the module `Std.Data.DTreeMap.Raw` for a variant of this type which is safe to use in
nested inductive types.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v w w₂

variable {α : Type u} {β : α → Type v} {cmp : α → α → Ordering}
private local instance : Coe (Type v) (α → Type v) where coe γ := fun _ => γ

namespace Std

/--
Dependent tree maps.

A tree map stores an assignment of keys to values. It depends on a comparator function that
defines an ordering on the keys and provides efficient order-dependent queries, such as retrieval
of the minimum or maximum.

To ensure that the operations behave as expected, the comparator function `cmp` should satisfy
certain laws that ensure a consistent ordering:

* If `a` is less than (or equal) to `b`, then `b` is greater than (or equal) to `a`
and vice versa (see the `OrientedCmp` typeclass).
* If `a` is less than or equal to `b` and `b` is, in turn, less than or equal to `c`, then `a`
is less than or equal to `c` (see the `TransCmp` typeclass).

Keys for which `cmp a b = Ordering.eq` are considered the same, i.e., there can be only one entry
with key either `a` or `b` in a tree map. Looking up either `a` or `b` always yields the same entry,
if any is present. The `get` operations of the _dependent_ tree map additionally require a
`LawfulEqCmp` instance to ensure that `cmp a b = .eq` always implies `a = b`, so that their
respective value types are equal.

To avoid expensive copies, users should make sure that the tree map is used linearly.

Internally, the tree maps are represented as size-bounded trees, a type of self-balancing binary
search tree with efficient order statistic lookups.

These tree maps contain a bundled well-formedness invariant, which means that they cannot
be used in nested inductive types. For these use cases, `Std.DTreeMap.Raw` and
`Std.DTreeMap.Raw.WF` unbundle the invariant from the tree map. When in doubt, prefer
`DTreeMap` over `DTreeMap.Raw`.
-/
structure DTreeMap (α : Type u) (β : α → Type v) (cmp : α → α → Ordering := by exact compare) where
  /-- Internal implementation detail of the tree map. -/
  inner : DTreeMap.Internal.Impl α β
  /-- Internal implementation detail of the tree map. -/
  wf : letI : Ord α := ⟨cmp⟩; inner.WF

namespace DTreeMap
open Internal (Impl)

/--
Creates a new empty tree map. It is also possible and recommended to
use the empty collection notations `∅` and `{}` to create an empty tree map. `simp` replaces
`empty` with `∅`.
-/
@[inline]
def empty : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Internal.Impl.empty, .empty⟩

instance : EmptyCollection (DTreeMap α β cmp) where
  emptyCollection := empty

instance : Inhabited (DTreeMap α β cmp) where
  default := ∅

@[simp]
theorem empty_eq_emptyc : (empty : DTreeMap α β cmp) = ∅ :=
  rfl

/--
Inserts the given mapping into the map. If there is already a mapping for the given key, then both
key and value will be replaced.
-/
@[inline]
def insert (t : DTreeMap α β cmp) (a : α) (b : β a) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨(t.inner.insert a b t.wf.balanced).impl, .insert t.wf⟩

instance : Singleton ((a : α) × β a) (DTreeMap α β cmp) where
  singleton e := (∅ : DTreeMap α β cmp).insert e.1 e.2

instance : Insert ((a : α) × β a) (DTreeMap α β cmp) where
  insert e s := s.insert e.1 e.2

instance : LawfulSingleton ((a : α) × β a) (DTreeMap α β cmp) where
  insert_emptyc_eq _ := rfl

/--
If there is no mapping for the given key, inserts the given mapping into the map. Otherwise,
returns the map unaltered.
-/
@[inline]
def insertIfNew (t : DTreeMap α β cmp) (a : α) (b : β a) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨(t.inner.insertIfNew a b t.wf.balanced).impl, t.wf.insertIfNew⟩

/--
Checks whether a key is present in a map and unconditionally inserts a value for the key.

Equivalent to (but potentially faster than) calling `contains` followed by `insert`.
-/
@[inline]
def containsThenInsert (t : DTreeMap α β cmp) (a : α) (b : β a) : Bool × DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsert a b t.wf.balanced
  (p.1, ⟨p.2.impl, t.wf.containsThenInsert⟩)

/--
Checks whether a key is present in a map and inserts a value for the key if it was not found.
If the returned `Bool` is `true`, then the returned map is unaltered. If the `Bool` is `false`,
then the returned map has a new value inserted.

Equivalent to (but potentially faster than) calling `contains` followed by `insertIfNew`.
-/
@[inline]
def containsThenInsertIfNew (t : DTreeMap α β cmp) (a : α) (b : β a) :
    Bool × DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsertIfNew a b t.wf.balanced
  (p.1, ⟨p.2.impl, t.wf.containsThenInsertIfNew⟩)

/--
Returns `true` if there is a mapping for the given key `a` or a key that is equal to `a` according
to the comparator `cmp`. There is also a `Prop`-valued version
of this: `a ∈ t` is equivalent to `t.contains a = true`.

Observe that this is different behavior than for lists: for lists, `∈` uses `=` and `contains` uses
`==` for equality checks, while for tree maps, both use the given comparator `cmp`.
-/
@[inline]
def contains (t : DTreeMap α β cmp) (a : α) : Bool :=
  letI : Ord α := ⟨cmp⟩; t.inner.contains a

instance : Membership α (DTreeMap α β cmp) where
  mem m a := m.contains a

instance {m : DTreeMap α β cmp} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs <| Decidable (m.contains a)

/-- Returns the number of mappings present in the map. -/
@[inline]
def size (t : DTreeMap α β cmp) : Nat :=
  t.inner.size

/-- Returns `true` if the tree map contains no mappings. -/
@[inline]
def isEmpty (t : DTreeMap α β cmp) : Bool :=
  t.inner.isEmpty

/-- Removes the mapping for the given key if it exists. -/
@[inline]
def erase (t : DTreeMap α β cmp) (a : α) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨(t.inner.erase a t.wf.balanced).impl, .erase t.wf⟩

/--
Tries to retrieve the mapping for the given key, returning `none` if no such mapping is present.

Uses the `LawfulEqCmp` instance to cast the retrieved value to the correct type.
-/
@[inline]
def get? [LawfulEqCmp cmp] (t : DTreeMap α β cmp) (a : α) : Option (β a) :=
  letI : Ord α := ⟨cmp⟩; t.inner.get? a

/--
Given a proof that a mapping for the given key is present, retrieves the mapping for the given key.

Uses the `LawfulEqCmp` instance to cast the retrieved value to the correct type.
-/
@[inline]
def get [LawfulEqCmp cmp] (t : DTreeMap α β cmp) (a : α) (h : a ∈ t) : β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.get a h

/--
Tries to retrieve the mapping for the given key, panicking if no such mapping is present.

Uses the `LawfulEqCmp` instance to cast the retrieved value to the correct type.
-/
@[inline]
def get! [LawfulEqCmp cmp] (t : DTreeMap α β cmp) (a : α) [Inhabited (β a)]  : β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.get! a

/--
Tries to retrieve the mapping for the given key, returning `fallback` if no such mapping is present.

Uses the `LawfulEqCmp` instance to cast the retrieved value to the correct type.
-/
@[inline]
def getD [LawfulEqCmp cmp] (t : DTreeMap α β cmp) (a : α) (fallback : β a) : β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.getD a fallback

namespace Const
open Internal (Impl)

variable {β : Type v}

/--
Tries to retrieve the mapping for the given key, returning `none` if no such mapping is present.
-/
@[inline]
def get? (t : DTreeMap α β cmp) (a : α) : Option β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.get? a t.inner

/--
Given a proof that a mapping for the given key is present, retrieves the mapping for the given key.
-/
@[inline]
def get (t : DTreeMap α β cmp) (a : α) (h : a ∈ t) : β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.get a t.inner h

/--
Tries to retrieve the mapping for the given key, panicking if no such mapping is present.
-/
@[inline]
def get! (t : DTreeMap α β cmp) (a : α) [Inhabited β] : β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.get! a t.inner

/--
Tries to retrieve the mapping for the given key, returning `fallback` if no such mapping is present.
-/
@[inline]
def getD (t : DTreeMap α β cmp) (a : α) (fallback : β) : β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getD a t.inner fallback

end Const

variable {δ : Type w} {m : Type w → Type w₂} [Monad m]

/-- Removes all mappings of the map for which the given function returns `false`. -/
@[inline]
def filter (f : (a : α) → β a → Bool) (t : DTreeMap α β cmp) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.filter f t.wf.balanced |>.impl, t.wf.filter⟩

/--
Folds the given monadic function over the mappings in the map in ascending order.
-/
@[inline]
def foldlM (f : δ → (a : α) → β a → m δ) (init : δ) (t : DTreeMap α β cmp) : m δ :=
  t.inner.foldlM f init

/--
Folds the given function over the mappings in the map in ascending order.
-/
@[inline]
def foldl (f : δ → (a : α) → β a → δ) (init : δ) (t : DTreeMap α β cmp) : δ :=
  t.inner.foldl f init

/-- Carries out a monadic action on each mapping in the tree map in ascending order. -/
@[inline]
def forM (f : (a : α) → β a → m PUnit) (t : DTreeMap α β cmp) : m PUnit :=
  t.inner.forM f

/-- Support for the `for` loop construct in `do` blocks. Iteration happens in ascending order. -/
@[inline]
def forIn (f : (a : α) → β a → δ → m (ForInStep δ)) (init : δ) (t : DTreeMap α β cmp) : m δ :=
  t.inner.forIn (fun c a b => f a b c) init

instance : ForM m (DTreeMap α β cmp) ((a : α) × β a) where
  forM t f := t.forM (fun a b => f ⟨a, b⟩)

instance : ForIn m (DTreeMap α β cmp) ((a : α) × β a) where
  forIn m init f := m.forIn (fun a b acc => f ⟨a, b⟩ acc) init

/-- Check if any element satisfes the predicate, short-circuiting if a predicate fails. -/
@[inline]
def any (t : DTreeMap α β cmp) (p : (a : α) → β a → Bool) : Bool := Id.run $ do
  for ⟨a, b⟩ in t do
    if p a b then return true
  return false

/-- Check if all elements satisfy the predicate, short-circuiting if a predicate fails. -/
@[inline]
def all (t : DTreeMap α β cmp) (p : (a : α) → β a → Bool) : Bool := Id.run $ do
  for ⟨a, b⟩ in t do
    if p a b = false then return false
  return true

/-- Returns a list of all keys present in the tree map in ascending  order. -/
@[inline]
def keys (t : DTreeMap α β cmp) : List α :=
  t.inner.keys

/-- Returns an array of all keys present in the tree map in ascending  order. -/
@[inline]
def keysArray (t : DTreeMap α β cmp) : Array α :=
  t.inner.keysArray

/-- Transforms the tree map into a list of mappings in ascending order. -/
@[inline]
def toList (t : DTreeMap α β cmp) : List ((a : α) × β a) :=
  t.inner.toList

/-- Transforms the tree map into a list of mappings in ascending order. -/
@[inline]
def toArray (t : DTreeMap α β cmp) : Array ((a : α) × β a) :=
  t.inner.toArray

/--
Returns a map that contains all mappings of `t₁` and `t₂`. In case that both maps contain the
same key `k` with respect to `cmp`, the provided function is used to determine the new value from
the respective values in `t₁` and `t₂`.

This function ensures that `t₁` is used linearly. It also uses the individual values in `t₁`
linearly if the merge function uses the second argument (i.e. the first of type `β a`) linearly.
Hence, as long as `t₁` is unshared, the performance characteristics follow the following imperative
description: Iterate over all mappings in `t₂`, inserting them into `t₁` if `t₁` does not contain a
conflicting mapping yet. If `t₁` does contain a conflicting mapping, use the given merge function to
merge the mapping in `t₂` into the mapping in `t₁`. Then return `t₁`.

Hence, the runtime of this method scales logarithmically in the size of `t₁` and linearly in the size of
`t₂` as long as `t₁` is unshared.
-/
@[inline]
def mergeWith [LawfulEqCmp cmp] (mergeFn : (a : α) → β a → β a → β a) (t₁ t₂ : DTreeMap α β cmp) :
    DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t₁.inner.mergeWith mergeFn t₂.inner t₁.wf.balanced |>.impl, t₁.wf.mergeWith⟩

namespace Const

variable {β : Type v}

@[inline, inherit_doc DTreeMap.toList]
def toList (t : DTreeMap α β cmp) : List (α × β) :=
  Impl.Const.toList t.inner

@[inline, inherit_doc DTreeMap.toArray]
def toArray (t : DTreeMap α β cmp) : Array (α × β) :=
  t.foldl (init := ∅) fun acc k v => acc.push ⟨k,v⟩

@[inline, inherit_doc DTreeMap.mergeWith]
def mergeWith (mergeFn : α → β → β → β) (t₁ t₂ : DTreeMap α β cmp) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩;
  ⟨Impl.Const.mergeWith mergeFn t₁.inner t₂.inner t₁.wf.balanced |>.impl, t₁.wf.constMergeBy⟩

end Const

/--
Erases multiple mappings from the tree map by iterating over the given collection and calling
`erase`.
-/
@[inline]
def eraseMany {ρ} [ForIn Id ρ α] (t : DTreeMap α β cmp) (l : ρ) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.eraseMany l t.wf.balanced, t.wf.eraseMany⟩

instance [Repr α] [(a : α) → Repr (β a)] : Repr (DTreeMap α β cmp) where
  reprPrec m prec := Repr.addAppParen ("DTreeMap.ofList " ++ repr m.toList) prec

end DTreeMap

end Std
