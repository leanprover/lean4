/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.DTreeMap.Raw

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

universe u v

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
structure DTreeMap (α : Type u) (β : α → Type v) (cmp : α → α → Ordering) where
  /-- Internal implementation detail of the tree map. -/
  inner : DTreeMap.Internal.Impl α β
  /-- Internal implementation detail of the tree map. -/
  wf : letI : Ord α := ⟨cmp⟩; inner.WF

namespace DTreeMap
open Internal (Impl)

@[inline, inherit_doc Raw.empty]
def empty : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Internal.Impl.empty, .empty⟩

instance : EmptyCollection (DTreeMap α β cmp) where
  emptyCollection := empty

instance : Inhabited (DTreeMap α β cmp) where
  default := ∅

@[inline, inherit_doc Raw.insert]
def insert (t : DTreeMap α β cmp) (a : α) (b : β a) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨(t.inner.insert a b t.wf.balanced).impl, .insert t.wf⟩

instance : Singleton ((a : α) × β a) (DTreeMap α β cmp) where
  singleton e := empty.insert e.1 e.2

instance : Insert ((a : α) × β a) (DTreeMap α β cmp) where
  insert e s := s.insert e.1 e.2

instance : LawfulSingleton ((a : α) × β a) (DTreeMap α β cmp) where
  insert_emptyc_eq _ := rfl

@[inline, inherit_doc Raw.insertIfNew]
def insertIfNew (t : DTreeMap α β cmp) (a : α) (b : β a) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨(t.inner.insertIfNew a b t.wf.balanced).impl, t.wf.insertIfNew⟩

@[inline, inherit_doc Raw.containsThenInsert]
def containsThenInsert (t : DTreeMap α β cmp) (a : α) (b : β a) : Bool × DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsert a b t.wf.balanced
  (p.1, ⟨p.2.impl, t.wf.containsThenInsert⟩)

@[inline, inherit_doc Raw.containsThenInsertIfNew]
def containsThenInsertIfNew (t : DTreeMap α β cmp) (a : α) (b : β a) :
    Bool × DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsertIfNew a b t.wf.balanced
  (p.1, ⟨p.2.impl, t.wf.containsThenInsertIfNew⟩)

@[inline, inherit_doc Raw.contains]
def contains (t : DTreeMap α β cmp) (a : α) : Bool :=
  letI : Ord α := ⟨cmp⟩; t.inner.contains a

instance : Membership α (DTreeMap α β cmp) where
  mem m a := m.contains a

instance {m : DTreeMap α β cmp} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs <| Decidable (m.contains a)

@[inline, inherit_doc Raw.size]
def size (t : DTreeMap α β cmp) : Nat :=
  t.inner.size

@[inline, inherit_doc Raw.isEmpty]
def isEmpty (t : DTreeMap α β cmp) : Bool :=
  t.inner.isEmpty

@[inline, inherit_doc Raw.erase]
def erase (t : DTreeMap α β cmp) (a : α) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨(t.inner.erase a t.wf.balanced).impl, .erase t.wf⟩

@[inline, inherit_doc Raw.get?]
def get? [LawfulEqCmp cmp] (t : DTreeMap α β cmp) (a : α) : Option (β a) :=
  letI : Ord α := ⟨cmp⟩; t.inner.get? a

@[inline, inherit_doc Raw.get]
def get [LawfulEqCmp cmp] (t : DTreeMap α β cmp) (a : α) (h : a ∈ t) : β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.get a h

@[inline, inherit_doc Raw.get!]
def get! [LawfulEqCmp cmp] (t : DTreeMap α β cmp) (a : α) [Inhabited (β a)]  : β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.get! a

@[inline, inherit_doc Raw.getD]
def getD [LawfulEqCmp cmp] (t : DTreeMap α β cmp) (a : α) (fallback : β a) : β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.getD a fallback

namespace Const
open Internal (Impl)

variable {β : Type v}

@[inline, inherit_doc Raw.Const.get?]
def get? (t : DTreeMap α β cmp) (a : α) : Option β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.get? a t.inner

@[inline, inherit_doc Raw.Const.get]
def get (t : DTreeMap α β cmp) (a : α) (h : a ∈ t) : β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.get a t.inner h

@[inline, inherit_doc Raw.Const.get!]
def get! (t : DTreeMap α β cmp) (a : α) [Inhabited β] : β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.get! a t.inner

@[inline, inherit_doc Raw.Const.getD]
def getD (t : DTreeMap α β cmp) (a : α) (fallback : β) : β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getD a t.inner fallback

end Const

universe w w₂
variable {δ : Type w} {m : Type w → Type w₂} [Monad m]

@[inline, inherit_doc Raw.filter]
def filter (f : (a : α) → β a → Bool) (t : DTreeMap α β cmp) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.filter f t.wf.balanced |>.impl, t.wf.filter⟩

@[inline, inherit_doc Raw.foldlM]
def foldlM (f : δ → (a : α) → β a → m δ) (init : δ) (t : DTreeMap α β cmp) : m δ :=
  t.inner.foldlM f init

@[inline, inherit_doc Raw.foldl]
def foldl (f : δ → (a : α) → β a → δ) (init : δ) (t : DTreeMap α β cmp) : δ :=
  t.inner.foldl f init

@[inline, inherit_doc Raw.forM]
def forM (f : (a : α) → β a → m PUnit) (t : DTreeMap α β cmp) : m PUnit :=
  t.inner.forM f

@[inline, inherit_doc Raw.forIn]
def forIn (f : (a : α) → β a → δ → m (ForInStep δ)) (init : δ) (t : DTreeMap α β cmp) : m δ :=
  t.inner.forIn (fun c a b => f a b c) init

instance : ForM m (DTreeMap α β cmp) ((a : α) × β a) where
  forM t f := t.forM (fun a b => f ⟨a, b⟩)

instance : ForIn m (DTreeMap α β cmp) ((a : α) × β a) where
  forIn m init f := m.forIn (fun a b acc => f ⟨a, b⟩ acc) init

@[inline, inherit_doc Raw.any]
def any (t : DTreeMap α β cmp) (p : (a : α) → β a → Bool) : Bool := Id.run $ do
  for ⟨a, b⟩ in t do
    if p a b then return true
  return false

@[inline, inherit_doc Raw.all]
def all (t : DTreeMap α β cmp) (p : (a : α) → β a → Bool) : Bool := Id.run $ do
  for ⟨a, b⟩ in t do
    if p a b = false then return false
  return true

@[inline, inherit_doc Raw.keys]
def keys (t : DTreeMap α β cmp) : List α :=
  t.inner.keys

@[inline, inherit_doc Raw.keysArray]
def keysArray (t : DTreeMap α β cmp) : Array α :=
  t.inner.keysArray

@[inline, inherit_doc Raw.toList]
def toList (t : DTreeMap α β cmp) : List ((a : α) × β a) :=
  t.inner.toList

@[inline, inherit_doc Raw.ofList]
def ofList (l : List ((a : α) × β a)) (cmp : α → α → Ordering) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩
  ⟨Impl.ofList l |>.impl, Impl.WF.ofList⟩

@[inline, inherit_doc Raw.ofList, deprecated ofList (since := "2025-02-06")]
def fromList (l : List ((a : α) × β a)) (cmp : α → α → Ordering) : DTreeMap α β cmp :=
  ofList l cmp

@[inline, inherit_doc Raw.toArray]
def toArray (t : DTreeMap α β cmp) : Array ((a : α) × β a) :=
  t.inner.toArray

@[inline, inherit_doc Raw.ofArray]
def ofArray (l : Array ((a : α) × β a)) (cmp : α → α → Ordering) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩
  ⟨Impl.ofArray l |>.impl, Impl.WF.ofArray⟩

@[inline, inherit_doc Raw.ofArray, deprecated ofArray (since := "2025-02-06")]
def fromArray (l : Array ((a : α) × β a)) (cmp : α → α → Ordering) : DTreeMap α β cmp :=
  ofArray l cmp

@[inline, inherit_doc Raw.mergeBy]
def mergeBy [LawfulEqCmp cmp] (mergeFn : (a : α) → β a → β a → β a) (t₁ t₂ : DTreeMap α β cmp) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t₁.inner.mergeBy mergeFn t₂.inner t₁.wf.balanced |>.impl, t₁.wf.mergeBy⟩

namespace Const

variable {β : Type v}

@[inline, inherit_doc Raw.Const.toList]
def toList (t : DTreeMap α β cmp) : List (α × β) :=
  Impl.Const.toList t.inner

@[inline, inherit_doc Raw.Const.ofList]
def ofList (l : List (α × β)) (cmp : α → α → Ordering) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩
  ⟨Impl.Const.ofList l |>.impl, Impl.WF.constOfList⟩

@[inline, inherit_doc Raw.Const.ofList, deprecated ofList (since := "2025-02-06")]
def fromList (l : List (α × β)) (cmp : α → α → Ordering) : DTreeMap α β cmp :=
  ofList l cmp

@[inline, inherit_doc Raw.Const.toArray]
def toArray (t : DTreeMap α β cmp) : Array (α × β) :=
  t.foldl (init := ∅) fun acc k v => acc.push ⟨k,v⟩

@[inline, inherit_doc Raw.Const.ofArray]
def ofArray (l : Array (α × β)) (cmp : α → α → Ordering) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.ofArray l |>.impl, Impl.WF.constOfArray⟩

@[inline, inherit_doc Raw.Const.ofArray, deprecated ofArray (since := "2025-02-06")]
def fromArray (l : Array (α × β)) (cmp : α → α → Ordering) : DTreeMap α β cmp :=
  ofArray l cmp

@[inline, inherit_doc Raw.Const.mergeBy]
def mergeBy (mergeFn : α → β → β → β) (t₁ t₂ : DTreeMap α β cmp) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩;
  ⟨Impl.Const.mergeBy mergeFn t₁.inner t₂.inner t₁.wf.balanced |>.impl, t₁.wf.constMergeBy⟩

end Const

@[inline, inherit_doc Raw.eraseMany]
def eraseMany {ρ} [ForIn Id ρ α] (t : DTreeMap α β cmp) (l : ρ) : DTreeMap α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.eraseMany l t.wf.balanced, t.wf.eraseMany⟩

instance [Repr α] [(a : α) → Repr (β a)] : Repr (DTreeMap α β cmp) where
  reprPrec m prec := Repr.addAppParen ("DTreeMap.ofList " ++ repr m.toList) prec

end DTreeMap

end Std
