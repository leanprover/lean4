/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DTreeMap.Internal.Impl

/-
# Dependent tree maps with unbundled well-formedness invariant

This file develops the type `Std.DTreeMap.Raw` of dependent tree maps with unbundled
well-formedness invariant.

This version is safe to use in nested inductive types. The well-formedness predicate is
available as `Std.DTreeMap.Raw.WF` and we prove in this file that all operations preserve
well-formedness. When in doubt, prefer `DTreeMap` over `DTreeMap.Raw`.

Lemmas about the operations on `Std.DTreeMap.Raw` will be available in the module
`Std.Data.DTreeMap.RawLemmas`.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v

variable {α : Type u} {β : α → Type v} {cmp : α → α → Ordering}
private local instance : Coe (Type v) (α → Type v) where coe γ := fun _ => γ

namespace Std

namespace DTreeMap

/--
Dependent tree maps without a bundled well-formedness invariant, suitable for use in nested
inductive types. The well-formedness invariant is called `Raw.WF`. When in doubt, prefer `DTreeMap`
over `DTreeMap.Raw`. Lemmas about the operations on `Std.DTreeMap.Raw` are available in the
module `Std.Data.DTreeMap.RawLemmas`.

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
-/
structure Raw (α : Type u) (β : α → Type v) (_cmp : α → α → Ordering) where
  /-- Internal implementation detail of the tree map. -/
  inner : Internal.Impl α β

namespace Raw

/--
Well-formedness predicate for tree maps. Users of `DTreeMap` will not need to interact with
this. Users of `DTreeMap.Raw` will need to provide proofs of `WF` to lemmas and should use lemmas
like `WF.empty` and `WF.insert` (which are always named exactly like the operations they are about)
to show that map operations preserve well-formedness. The constructors of this type are internal
implementation details and should not be accessed by users.
-/
structure WF (t : Raw α β cmp) where
  /-- Internal implementation detail of the tree map. -/
  out : letI : Ord α := ⟨cmp⟩; t.inner.WF

instance {t : Raw α β cmp} : Coe t.WF (letI : Ord α := ⟨cmp⟩; t.inner.WF) where
  coe h := h.out

/--
Creates a new empty tree map. It is also possible to
use the empty collection notations `∅` and `{}` to create an empty tree map.
-/
@[inline]
def empty : Raw α β cmp :=
  ⟨Internal.Impl.empty⟩

instance : EmptyCollection (Raw α β cmp) := ⟨empty⟩

instance : Inhabited (Raw α β cmp) := ⟨∅⟩

/--
Inserts the given mapping into the map. If there is already a mapping for the given key, then both
key and value will be replaced.
-/
@[inline]
def insert (t : Raw α β cmp) (a : α) (b : β a) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.insert! a b⟩

/--
Inserts the given mapping into the map. If there is already a mapping for the given key, then both
key and value will be replaced.
-/
@[inline]
def insertFast (t : Raw α β cmp) (h : t.WF) (a : α) (b : β a) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨(t.inner.insert a b h.out.balanced).impl⟩

instance : Singleton ((a : α) × β a) (Raw α β cmp) where
  singleton e := empty.insert e.1 e.2

instance : Insert ((a : α) × β a) (Raw α β cmp) where
  insert e s := s.insert e.1 e.2

instance : LawfulSingleton ((a : α) × β a) (Raw α β cmp) where
  insert_emptyc_eq _ := rfl

/--
If there is no mapping for the given key, inserts the given mapping into the map. Otherwise,
returns the map unaltered.
-/
@[inline] def insertIfNew (t : Raw α β cmp) (a : α) (b : β a) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.insertIfNew! a b⟩

/--
Checks whether a key is present in a map and inserts a value for the key if it was not found.

If the returned `Bool` is `true`, then the returned map is unaltered. If the `Bool` is `false`, then
the returned map has a new value inserted.

Equivalent to (but potentially faster than) calling `contains` followed by `insertIfNew`.
-/
@[inline]
def containsThenInsert (t : Raw α β cmp) (a : α) (b : β a) : Bool × Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsert! a b
  (p.1, ⟨p.2⟩)

/--
Checks whether a key is present in a map and inserts a value for the key if it was not found.

If the returned `Bool` is `true`, then the returned map is unaltered. If the `Bool` is `false`, then
the returned map has a new value inserted.

Equivalent to (but potentially faster than) calling `contains` followed by `insertIfNew`.
-/
@[inline] def containsThenInsertIfNew (t : Raw α β cmp) (a : α) (b : β a) :
    Bool × Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsertIfNew! a b
  (p.1, ⟨p.2⟩)

/--
Returns `true` if there is a mapping for the given key `a` or a key that is equal to `a` according
to the comparator `cmp`. There is also a `Prop`-valued version
of this: `a ∈ t` is equivalent to `t.contains a = true`.

Observe that this is different behavior than for lists: for lists, `∈` uses `=` and `contains` uses
`==` for equality checks, while for tree maps, both use the given comparator `cmp`.
-/
@[inline]
def contains (t : Raw α β cmp) (a : α) : Bool :=
  letI : Ord α := ⟨cmp⟩; t.inner.contains a

instance : Membership α (Raw α β cmp) where
  mem t a := t.contains a

instance {t : Raw α β cmp} {a : α} : Decidable (a ∈ t) :=
  inferInstanceAs <| Decidable (t.contains a)

/-- Returns the number of mappings present in the map. -/
@[inline]
def size (t : Raw α β cmp) : Nat :=
  t.inner.size

/--
Returns `true` if the tree map contains no mappings.
-/
@[inline]
def isEmpty (t : Raw α β cmp) : Bool :=
  t.inner.isEmpty

/--
Returns `true` if the tree map contains exactly one mapping.
-/
@[inline]
def isSingleton (t : Raw α β cmp) : Bool :=
  t.inner.isSingleton

/-- Removes the mapping for the given key if it exists. -/
@[inline]
def erase (t : Raw α β cmp) (a : α) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.erase! a⟩

/--
Tries to retrieve the mapping for the given key, returning `none` if no such mapping is present.

Uses the `LawfulEqCmp` instance to cast the retrieved value to the correct type.
-/
@[inline]
def get? [LawfulEqCmp cmp] (t : Raw α β cmp) (a : α) : Option (β a) :=
  letI : Ord α := ⟨cmp⟩; t.inner.get? a

/--
Given a proof that a mapping for the given key is present, returns the value associated .

Uses the `LawfulEqCmp` instance to cast the retrieved value to the correct type.
-/
@[inline]
def get [LawfulEqCmp cmp] (t : Raw α β cmp) (a : α) (h : a ∈ t) : β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.get a h

/--
Tries to retrieve the mapping for the given key, panicking if no such mapping is present.

Uses the `LawfulEqCmp` instance to cast the retrieved value to the correct type.
-/
@[inline]
def get! [LawfulEqCmp cmp] (t : Raw α β cmp) (a : α) [Inhabited (β a)]  : β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.get! a

/--
Tries to retrieve the mapping for the given key, returning `fallback` if no such mapping is present.

Uses the `LawfulEqCmp` instance to cast the retrieved value to the correct type.
-/
@[inline]
def getD [LawfulEqCmp cmp] (t : Raw α β cmp) (a : α) (fallback : β a) : β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.getD a fallback

namespace Const
open Internal (Impl)

variable {β : Type v}

/--
Retrieves the mapping for the given key. Ensures that such a mapping exists by requiring a proof
of `a ∈ m`.
-/
@[inline] def get? (t : Raw α β cmp) (a : α) : Option β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.get? a t.inner

/--
Given a proof that a mapping for the given key is present, returns the value associated .
-/
@[inline]
def get (t : Raw α β cmp) (a : α) (h : a ∈ t) : β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.get a t.inner h


/--
Tries to retrieve the mapping for the given key, panicking if no such mapping is present.
-/
@[inline]
def get! (t : Raw α β cmp) (a : α) [Inhabited β] : β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.get! a t.inner


/--
Tries to retrieve the mapping for the given key, returning `fallback` if no such mapping is present.
-/
@[inline]
def getD (t : Raw α β cmp) (a : α) (fallback : β) : β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getD a t.inner fallback

end Const

universe w w₂
variable {δ : Type w} {m : Type w → Type w₂} [Monad m]

/-- Removes all mappings of the map for which the given function returns `false`. -/
@[inline]
def filter (f : (a : α) → β a → Bool) (t : Raw α β cmp) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.filter! f⟩

/--
Folds the given monadic function over the mappings in the map in ascending order.
-/
@[inline]
def foldlM (f : δ → (a : α) → β a → m δ) (init : δ) (t : Raw α β cmp) : m δ :=
  t.inner.foldlM f init

/--
Folds the given function over the mappings in the map in ascending order.
-/
@[inline]
def foldl (f : δ → (a : α) → β a → δ) (init : δ) (t : Raw α β cmp) : δ :=
  t.inner.foldl f init

/-- Carries out a monadic action on each mapping in the tree map in ascending order. -/
@[inline]
def forM (f : (a : α) → β a → m PUnit) (t : Raw α β cmp) : m PUnit :=
  t.inner.forM f

/-- Support for the `for` loop construct in `do` blocks. Iteration happens in ascending order. -/
@[inline]
def forIn (f : (a : α) → β a → δ → m (ForInStep δ)) (init : δ) (t : Raw α β cmp) : m δ :=
  t.inner.forIn (fun c a b => f a b c) init

instance : ForM m (Raw α β cmp) ((a : α) × β a) where
  forM t f := t.forM (fun a b => f ⟨a, b⟩)

instance : ForIn m (Raw α β cmp) ((a : α) × β a) where
  forIn t init f := t.forIn (fun a b acc => f ⟨a, b⟩ acc) init

/-- Check if any element satisfes the predicate, short-circuiting if a predicate fails. -/
@[inline]
def any (t : Raw α β cmp) (p : (a : α) → β a → Bool) : Bool := Id.run $ do
  for ⟨a, b⟩ in t do
    if p a b then return true
  return false

/-- Check if all elements satisfy the predicate, short-circuiting if a predicate fails. -/
@[inline]
def all (t : Raw α β cmp) (p : (a : α) → β a → Bool) : Bool := Id.run $ do
  for ⟨a, b⟩ in t do
    if p a b = false then return false
  return true

/-- Returns a list of all keys present in the tree map in some order. -/
@[inline]
def keys (t : Raw α β cmp) : List α :=
  t.inner.keys

/-- Returns an array of all keys present in the tree map in some order. -/
@[inline]
def keysArray (t : Raw α β cmp) : Array α :=
  t.inner.keysArray

/-- Transforms the tree map into a list of mappings in ascending order. -/
@[inline]
def toList (t : Raw α β cmp) : List ((a : α) × β a) :=
  t.inner.toList

/-- Transforms a list of mappings into a tree map. -/
@[inline]
def ofList (l : List ((a : α) × β a)) (cmp : α → α → Ordering) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Internal.Impl.ofList l |>.impl⟩

@[inline, inherit_doc ofList, deprecated ofList (since := "2025-02-06")]
def fromList (l : List ((a : α) × β a)) (cmp : α → α → Ordering) : Raw α β cmp :=
  ofList l cmp

/-- Transforms the tree map into a list of mappings in ascending order. -/
@[inline]
def toArray (t : Raw α β cmp) : Array ((a : α) × β a) :=
  t.inner.toArray

/-- Transforms an array of mappings into a tree map. -/
@[inline]
def ofArray (l : Array ((a : α) × β a)) (cmp : α → α → Ordering) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Internal.Impl.ofArray l |>.impl⟩

@[inline, inherit_doc ofArray, deprecated ofArray (since := "2025-02-06")]
def fromArray (l : Array ((a : α) × β a)) (cmp : α → α → Ordering) : Raw α β cmp :=
  ofArray l cmp

/--
Returns a map that contains all mappings of `t₁` and `t₂`. In case that both maps contain the
same key `k` with respect to `cmp`, the provided function is used to determine the new value from
the respective values in `t₁` and `t₂`.
-/
@[inline]
def mergeBy [LawfulEqCmp cmp] (mergeFn : (a : α) → β a → β a → β a) (t₁ t₂ : Raw α β cmp) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t₁.inner.mergeBy! mergeFn t₂.inner⟩

namespace Const
open Internal (Impl)

variable {β : Type v}

@[inline, inherit_doc Raw.toList]
def toList (t : Raw α β cmp) : List (α × β) :=
  Impl.Const.toList t.inner

@[inline, inherit_doc Raw.ofList]
def ofList (l : List (α × β)) (cmp : α → α → Ordering) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.ofList l |>.impl⟩

@[inline, inherit_doc Raw.ofList, deprecated ofList (since := "2025-02-06")]
def fromList (l : List (α × β)) (cmp : α → α → Ordering) : Raw α β cmp :=
  ofList l cmp

@[inline, inherit_doc Raw.toArray]
def toArray (t : Raw α β cmp) : Array (α × β) :=
  Impl.Const.toArray t.inner

@[inline, inherit_doc Raw.ofArray]
def ofArray (l : Array (α × β)) (cmp : α → α → Ordering) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.ofArray l |>.impl⟩

@[inline, inherit_doc Raw.ofArray, deprecated ofArray (since := "2025-02-06")]
def fromArray (l : Array (α × β)) (cmp : α → α → Ordering) : Raw α β cmp :=
  ofArray l cmp

@[inline, inherit_doc Raw.mergeBy]
def mergeBy (mergeFn : α → β → β → β) (t₁ t₂ : Raw α β cmp) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.mergeBy! mergeFn t₁.inner t₂.inner⟩

end Const

/--
Erases multiple mappings from the tree map by iterating over the given collection and calling erase.
-/
@[inline]
def eraseMany {ρ} [ForIn Id ρ α] (t : Raw α β cmp) (l : ρ) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.eraseMany! l⟩

instance [Repr α] [(a : α) → Repr (β a)] : Repr (Raw α β cmp) where
  reprPrec m prec := Repr.addAppParen ("DTreeMap.Raw.ofList " ++ repr m.toList) prec

end Raw

end DTreeMap

end Std
