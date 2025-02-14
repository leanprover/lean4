/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.DTreeMap.Internal.WF.Def
import Std.Data.DTreeMap.Basic

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

universe u v w w₂

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
structure Raw (α : Type u) (β : α → Type v) (_cmp : α → α → Ordering := by exact compare) where
  /-- Internal implementation detail of the tree map. -/
  inner : Internal.Impl α β

namespace Raw
open Internal (Impl)

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

@[inline, inherit_doc DTreeMap.empty]
def empty : Raw α β cmp :=
  ⟨Internal.Impl.empty⟩

instance : EmptyCollection (Raw α β cmp) := ⟨empty⟩

instance : Inhabited (Raw α β cmp) := ⟨∅⟩

@[simp]
theorem empty_eq_emptyc : (empty : Raw α β cmp) = ∅ :=
  rfl

@[inline, inherit_doc DTreeMap.insert]
def insert (t : Raw α β cmp) (a : α) (b : β a) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.insert! a b⟩

instance : Singleton ((a : α) × β a) (Raw α β cmp) where
  singleton e := (∅ : Raw α β cmp).insert e.1 e.2

instance : Insert ((a : α) × β a) (Raw α β cmp) where
  insert e s := s.insert e.1 e.2

instance : LawfulSingleton ((a : α) × β a) (Raw α β cmp) where
  insert_emptyc_eq _ := rfl

@[inline, inherit_doc DTreeMap.insertIfNew]
def insertIfNew (t : Raw α β cmp) (a : α) (b : β a) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.insertIfNew! a b⟩

@[inline, inherit_doc DTreeMap.containsThenInsert]
def containsThenInsert (t : Raw α β cmp) (a : α) (b : β a) : Bool × Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsert! a b
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc DTreeMap.containsThenInsertIfNew]
def containsThenInsertIfNew (t : Raw α β cmp) (a : α) (b : β a) :
    Bool × Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsertIfNew! a b
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc DTreeMap.contains]
def contains (t : Raw α β cmp) (a : α) : Bool :=
  letI : Ord α := ⟨cmp⟩; t.inner.contains a

instance : Membership α (Raw α β cmp) where
  mem t a := t.contains a

instance {t : Raw α β cmp} {a : α} : Decidable (a ∈ t) :=
  inferInstanceAs <| Decidable (t.contains a)

@[inline, inherit_doc DTreeMap.size]
def size (t : Raw α β cmp) : Nat :=
  t.inner.size

@[inline, inherit_doc DTreeMap.isEmpty]
def isEmpty (t : Raw α β cmp) : Bool :=
  t.inner.isEmpty

@[inline, inherit_doc DTreeMap.erase]
def erase (t : Raw α β cmp) (a : α) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.erase! a⟩

@[inline, inherit_doc DTreeMap.get?]
def get? [LawfulEqCmp cmp] (t : Raw α β cmp) (a : α) : Option (β a) :=
  letI : Ord α := ⟨cmp⟩; t.inner.get? a

@[inline, inherit_doc get?, deprecated get? (since := "2025-02-12")]
def find? [LawfulEqCmp cmp] (t : Raw α β cmp) (a : α) : Option (β a) :=
  t.get? a

@[inline, inherit_doc DTreeMap.get]
def get [LawfulEqCmp cmp] (t : Raw α β cmp) (a : α) (h : a ∈ t) : β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.get a h

@[inline, inherit_doc DTreeMap.get!]
def get! [LawfulEqCmp cmp] (t : Raw α β cmp) (a : α) [Inhabited (β a)]  : β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.get! a

@[inline, inherit_doc get!, deprecated get! (since := "2025-02-12")]
def find! [LawfulEqCmp cmp] (t : Raw α β cmp) (a : α) [Inhabited (β a)]  : β a :=
  t.get! a

@[inline, inherit_doc DTreeMap.getD]
def getD [LawfulEqCmp cmp] (t : Raw α β cmp) (a : α) (fallback : β a) : β a :=
  letI : Ord α := ⟨cmp⟩; t.inner.getD a fallback

@[inline, inherit_doc getD, deprecated getD (since := "2025-02-12")]
def findD [LawfulEqCmp cmp] (t : Raw α β cmp) (a : α) (fallback : β a) : β a :=
  t.getD a fallback

namespace Const

variable {β : Type v}

@[inline, inherit_doc DTreeMap.get?]
def get? (t : Raw α β cmp) (a : α) : Option β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.get? a t.inner

@[inline, inherit_doc get?, deprecated get? (since := "2025-02-12")]
def find? (t : Raw α β cmp) (a : α) : Option β :=
  get? t a

@[inline, inherit_doc DTreeMap.get]
def get (t : Raw α β cmp) (a : α) (h : a ∈ t) : β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.get a t.inner h

@[inline, inherit_doc DTreeMap.get!]
def get! (t : Raw α β cmp) (a : α) [Inhabited β] : β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.get! a t.inner

@[inline, inherit_doc get!, deprecated get! (since := "2025-02-12")]
def find! (t : Raw α β cmp) (a : α) [Inhabited β] : β :=
  get! t a

@[inline, inherit_doc DTreeMap.getD]
def getD (t : Raw α β cmp) (a : α) (fallback : β) : β :=
  letI : Ord α := ⟨cmp⟩; Impl.Const.getD a t.inner fallback

@[inline, inherit_doc getD, deprecated getD (since := "2025-02-12")]
def findD (t : Raw α β cmp) (a : α) (fallback : β) : β :=
  getD t a fallback

end Const

variable {δ : Type w} {m : Type w → Type w₂} [Monad m]

@[inline, inherit_doc DTreeMap.filter]
def filter (f : (a : α) → β a → Bool) (t : Raw α β cmp) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.filter! f⟩

@[inline, inherit_doc DTreeMap.foldlM]
def foldlM (f : δ → (a : α) → β a → m δ) (init : δ) (t : Raw α β cmp) : m δ :=
  t.inner.foldlM f init

@[inline, inherit_doc foldlM, deprecated foldlM (since := "2025-02-12")]
def foldM (f : δ → (a : α) → β a → m δ) (init : δ) (t : Raw α β cmp) : m δ :=
  t.foldlM f init

@[inline, inherit_doc DTreeMap.foldl]
def foldl (f : δ → (a : α) → β a → δ) (init : δ) (t : Raw α β cmp) : δ :=
  t.inner.foldl f init

@[inline, inherit_doc foldl, deprecated foldl (since := "2025-02-12")]
def fold (f : δ → (a : α) → β a → δ) (init : δ) (t : Raw α β cmp) : δ :=
  t.foldl f init

@[inline, inherit_doc DTreeMap.foldrM]
def foldrM (f : δ → (a : α) → β a → m δ) (init : δ) (t : Raw α β cmp) : m δ :=
  t.inner.foldrM f init

@[inline, inherit_doc DTreeMap.foldr]
def foldr (f : δ → (a : α) → β a → δ) (init : δ) (t : Raw α β cmp) : δ :=
  t.inner.foldr f init

@[inline, inherit_doc foldr, deprecated foldr (since := "2025-02-12")]
def revFold (f : δ → (a : α) → β a → δ) (init : δ) (t : Raw α β cmp) : δ :=
  foldr f init t

@[inline, inherit_doc DTreeMap.forM]
def forM (f : (a : α) → β a → m PUnit) (t : Raw α β cmp) : m PUnit :=
  t.inner.forM f

@[inline, inherit_doc DTreeMap.forIn]
def forIn (f : (a : α) → β a → δ → m (ForInStep δ)) (init : δ) (t : Raw α β cmp) : m δ :=
  t.inner.forIn (fun c a b => f a b c) init

instance : ForM m (Raw α β cmp) ((a : α) × β a) where
  forM t f := t.forM (fun a b => f ⟨a, b⟩)

instance : ForIn m (Raw α β cmp) ((a : α) × β a) where
  forIn t init f := t.forIn (fun a b acc => f ⟨a, b⟩ acc) init

@[inline, inherit_doc DTreeMap.any]
def any (t : Raw α β cmp) (p : (a : α) → β a → Bool) : Bool := Id.run $ do
  for ⟨a, b⟩ in t do
    if p a b then return true
  return false

@[inline, inherit_doc DTreeMap.all]
def all (t : Raw α β cmp) (p : (a : α) → β a → Bool) : Bool := Id.run $ do
  for ⟨a, b⟩ in t do
    if p a b = false then return false
  return true

@[inline, inherit_doc DTreeMap.keys]
def keys (t : Raw α β cmp) : List α :=
  t.inner.keys

@[inline, inherit_doc DTreeMap.keysArray]
def keysArray (t : Raw α β cmp) : Array α :=
  t.inner.keysArray

@[inline, inherit_doc DTreeMap.toList]
def toList (t : Raw α β cmp) : List ((a : α) × β a) :=
  t.inner.toList

/-- Transforms a list of mappings into a tree map. -/
@[inline]
def ofList (l : List ((a : α) × β a)) (cmp : α → α → Ordering := by exact compare) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩
  ⟨Impl.ofList l⟩

@[inline, inherit_doc ofList, deprecated ofList (since := "2025-02-12")]
def fromList (l : List ((a : α) × β a)) (cmp : α → α → Ordering) : Raw α β cmp :=
  ofList l cmp

@[inline, inherit_doc DTreeMap.toArray]
def toArray (t : Raw α β cmp) : Array ((a : α) × β a) :=
  t.inner.toArray

/-- Transforms an array of mappings into a tree map. -/
@[inline]
def ofArray (a : Array ((a : α) × β a)) (cmp : α → α → Ordering := by exact compare) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩
  ⟨Impl.ofArray a⟩

@[inline, inherit_doc ofArray, deprecated ofArray (since := "2025-02-12")]
def fromArray (a : Array ((a : α) × β a)) (cmp : α → α → Ordering) : Raw α β cmp :=
  ofArray a cmp

@[inline, inherit_doc DTreeMap.mergeWith]
def mergeWith [LawfulEqCmp cmp] (mergeFn : (a : α) → β a → β a → β a) (t₁ t₂ : Raw α β cmp) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t₁.inner.mergeWith! mergeFn t₂.inner⟩

@[inline, inherit_doc mergeWith, deprecated mergeWith (since := "2025-02-12")]
def mergeBy [LawfulEqCmp cmp] (mergeFn : (a : α) → β a → β a → β a) (t₁ t₂ : Raw α β cmp) :
    Raw α β cmp :=
  mergeWith mergeFn t₁ t₂

namespace Const
open Internal (Impl)

variable {β : Type v}

@[inline, inherit_doc DTreeMap.Const.toList]
def toList (t : Raw α β cmp) : List (α × β) :=
  Impl.Const.toList t.inner

@[inline, inherit_doc DTreeMap.Const.ofList]
def ofList (l : List (α × β)) (cmp : α → α → Ordering := by exact compare) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.ofList l⟩

@[inline, inherit_doc DTreeMap.Const.unitOfList]
def unitOfList (l : List α) (cmp : α → α → Ordering := by exact compare) : Raw α Unit cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.unitOfList l⟩

@[inline, inherit_doc DTreeMap.Const.toArray]
def toArray (t : Raw α β cmp) : Array (α × β) :=
  Impl.Const.toArray t.inner

@[inline, inherit_doc DTreeMap.Const.ofArray]
def ofArray (a : Array (α × β)) (cmp : α → α → Ordering := by exact compare) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.ofArray a⟩

@[inline, inherit_doc DTreeMap.Const.ofArray]
def unitOfArray (a : Array α) (cmp : α → α → Ordering := by exact compare) : Raw α Unit cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.unitOfArray a⟩

@[inline, inherit_doc DTreeMap.Const.mergeWith]
def mergeWith (mergeFn : α → β → β → β) (t₁ t₂ : Raw α β cmp) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.mergeWith! mergeFn t₁.inner t₂.inner⟩

@[inline, inherit_doc mergeWith, deprecated mergeWith (since := "2025-02-12")]
def mergeBy (mergeFn : α → β → β → β) (t₁ t₂ : Raw α β cmp) : Raw α β cmp :=
  mergeWith mergeFn t₁ t₂

end Const

@[inline, inherit_doc DTreeMap.insertMany]
def insertMany {ρ} [ForIn Id ρ ((a : α) × β a)] (t : Raw α β cmp) (l : ρ) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.insertMany! l⟩

@[inline, inherit_doc DTreeMap.eraseMany]
def eraseMany {ρ} [ForIn Id ρ α] (t : Raw α β cmp) (l : ρ) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨t.inner.eraseMany! l⟩

namespace Const

variable {β : Type v}

@[inline, inherit_doc DTreeMap.Const.insertMany]
def insertMany {ρ} [ForIn Id ρ (α × β)] (t : Raw α β cmp) (l : ρ) : Raw α β cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.insertMany! t.inner l⟩

@[inline, inherit_doc DTreeMap.Const.insertManyIfNewUnit]
def insertManyIfNewUnit {ρ} [ForIn Id ρ α] (t : Raw α Unit cmp) (l : ρ) : Raw α Unit cmp :=
  letI : Ord α := ⟨cmp⟩; ⟨Impl.Const.insertManyIfNewUnit! t.inner l⟩

end Const

instance [Repr α] [(a : α) → Repr (β a)] : Repr (Raw α β cmp) where
  reprPrec m prec := Repr.addAppParen ("DTreeMap.Raw.ofList " ++ repr m.toList) prec

end Raw

end DTreeMap

end Std
