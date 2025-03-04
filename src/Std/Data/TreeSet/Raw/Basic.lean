/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
prelude
import Std.Data.TreeMap.Raw.Basic
import Std.Data.TreeSet.Basic

/-
# Tree sets with unbundled well-formedness invariant

This file develops the type `Std.TreeSet.Raw` of tree sets with unbundled
well-formedness invariant.

This version is safe to use in nested inductive types. The well-formedness predicate is
available as `Std.TreeSet.Raw.WF` and we prove in this file that all operations preserve
well-formedness. When in doubt, prefer `TreeSet` over `TreeSet.Raw`.

Lemmas about the operations on `Std.TreeSet.Raw` will be available in the module
`Std.Data.TreeSet.Raw.Lemmas`.
-/

set_option autoImplicit false
set_option linter.missingDocs true

universe u v w w₂

variable {α : Type u} {cmp : α → α → Ordering}

namespace Std

namespace TreeSet

/--
Tree sets without a bundled well-formedness invariant, suitable for use in nested
inductive types. The well-formedness invariant is called `Raw.WF`. When in doubt, prefer `TreeSet`
over `TreeSet.Raw`. Lemmas about the operations on `Std.TreeSet.Raw` are available in the
module `Std.Data.TreeSet.Raw.Lemmas`.

A tree set stores elements of a certain type in a certain order. It depends on a comparator function
that defines an ordering on the keys and provides efficient order-dependent queries, such as
retrieval of the minimum or maximum.

To ensure that the operations behave as expected, the comparator function `cmp` should satisfy
certain laws that ensure a consistent ordering:

* If `a` is less than (or equal) to `b`, then `b` is greater than (or equal) to `a`
and vice versa (see the `OrientedCmp` typeclass).
* If `a` is less than or equal to `b` and `b` is, in turn, less than or equal to `c`, then `a`
is less than or equal to `c` (see the `TransCmp` typeclass).

Keys for which `cmp a b = Ordering.eq` are considered the same, i.e only one of them
can be contained in a single tree set at the same time.

To avoid expensive copies, users should make sure that the tree set is used linearly.

Internally, the tree sets are represented as size-bounded trees, a type of self-balancing binary
search tree with efficient order statistic lookups.
-/
structure Raw (α : Type u) (cmp : α → α → Ordering := by exact compare) where
  /-- Internal implementation detail of the tree set. -/
  inner : TreeMap.Raw α Unit cmp

namespace Raw

/--
Well-formedness predicate for tree sets. Users of `TreeSet` will not need to interact with
this. Users of `TreeSet.Raw` will need to provide proofs of `WF` to lemmas and should use lemmas
like `WF.empty` and `WF.insert` (which are always named exactly like the operations they are about)
to show that set operations preserve well-formedness. The constructors of this type are internal
implementation details and should not be accessed by users.
-/
structure WF (t : Raw α cmp) where
  /-- Internal implementation detail of the tree map. -/
  out : t.inner.WF

instance {t : Raw α cmp} : Coe t.WF t.inner.WF where
  coe t := t.out

@[inline, inherit_doc TreeSet.empty]
def empty : Raw α cmp :=
  ⟨TreeMap.Raw.empty⟩

instance : EmptyCollection (Raw α cmp) where
  emptyCollection := empty

instance : Inhabited (Raw α cmp) where
  default := ∅

@[simp]
theorem empty_eq_emptyc : (empty : Raw α cmp) = ∅ :=
  rfl

@[inline, inherit_doc TreeSet.empty]
def insert (l : Raw α cmp) (a : α) : Raw α cmp :=
  ⟨l.inner.insertIfNew a ()⟩

instance : Singleton α (Raw α cmp) where
  singleton e := (∅ : Raw α cmp).insert e

instance : Insert α (Raw α cmp) where
  insert e s := s.insert e

instance : LawfulSingleton α (Raw α cmp) where
  insert_emptyc_eq _ := rfl

@[inline, inherit_doc TreeSet.empty]
def containsThenInsert (t : Raw α cmp) (a : α) : Bool × Raw α cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsertIfNew a ()
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc TreeSet.empty]
def contains (l : Raw α cmp) (a : α) : Bool :=
  l.inner.contains a

instance : Membership α (Raw α cmp) where
  mem t a := t.contains a

instance {t : Raw α cmp} {a : α} : Decidable (a ∈ t) :=
  inferInstanceAs <| Decidable (t.contains a)

@[inline, inherit_doc TreeSet.empty]
def size (t : Raw α cmp) : Nat :=
  t.inner.size

@[inline, inherit_doc TreeSet.empty]
def isEmpty (t : Raw α cmp) : Bool :=
  t.inner.isEmpty

@[inline, inherit_doc TreeSet.empty]
def erase (t : Raw α cmp) (a : α) : Raw α cmp :=
  ⟨t.inner.erase a⟩

@[inline, inherit_doc TreeSet.get?]
def get? (t : Raw α cmp) (a : α) : Option α :=
  t.inner.getKey? a

@[inline, inherit_doc TreeSet.get]
def get (t : Raw α cmp) (a : α) (h : a ∈ t) : α :=
  t.inner.getKey a h

@[inline, inherit_doc TreeSet.get!]
def get! [Inhabited α] (t : Raw α cmp) (a : α) : α :=
  t.inner.getKey! a

@[inline, inherit_doc TreeSet.getD]
def getD (t : Raw α cmp) (a : α) (fallback : α) : α :=
  t.inner.getKeyD a fallback

@[inline, inherit_doc TreeSet.min?]
def min? (t : Raw α cmp) : Option α :=
  TreeMap.Raw.minKey? t.inner

/-!
We do not provide `min` for the raw trees.
-/

@[inline, inherit_doc TreeSet.min!]
def min! [Inhabited α] (t : Raw α cmp) : α :=
  TreeMap.Raw.minKey! t.inner

@[inline, inherit_doc TreeSet.minD]
def minD (t : Raw α cmp) (fallback : α) : α :=
  TreeMap.Raw.minKeyD t.inner fallback

@[inline, inherit_doc TreeSet.max?]
def max? (t : Raw α cmp) : Option α :=
  TreeMap.Raw.maxKey? t.inner

/-!
We do not provide `max` for the raw trees.
-/

@[inline, inherit_doc TreeSet.max!]
def max! [Inhabited α] (t : Raw α cmp) : α :=
  TreeMap.Raw.maxKey! t.inner

@[inline, inherit_doc TreeSet.maxD]
def maxD (t : Raw α cmp) (fallback : α) : α :=
  TreeMap.Raw.maxKeyD t.inner fallback

@[inline, inherit_doc TreeSet.atIdx?]
def atIdx? (t : Raw α cmp) (n : Nat) : Option α :=
  TreeMap.Raw.keyAtIndex? t.inner n

/-!
We do not provide `entryAtIdx` for the raw trees.
-/

@[inline, inherit_doc TreeSet.atIdx!]
def atIdx! [Inhabited α] (t : Raw α cmp) (n : Nat) : α :=
  TreeMap.Raw.keyAtIndex! t.inner n

@[inline, inherit_doc TreeSet.atIdxD]
def atIdxD (t : Raw α cmp) (n : Nat) (fallback : α) : α :=
  TreeMap.Raw.keyAtIndexD t.inner n fallback

@[inline, inherit_doc TreeSet.getGE?]
def getGE? (t : Raw α cmp) (k : α) : Option α :=
  TreeMap.Raw.getKeyGE? t.inner k

@[inline, inherit_doc TreeSet.getGT?]
def getGT? (t : Raw α cmp) (k : α) : Option α :=
  TreeMap.Raw.getKeyGT? t.inner k

@[inline, inherit_doc TreeSet.getLE?]
def getLE? (t : Raw α cmp) (k : α) : Option α :=
  TreeMap.Raw.getKeyLE? t.inner k

@[inline, inherit_doc TreeSet.getLT?]
def getLT? (t : Raw α cmp) (k : α) : Option α :=
  TreeMap.Raw.getKeyLT? t.inner k

/-!
We do not provide `getGE`, `getGT`, `getLE`, `getLT` for the raw trees.
-/

@[inline, inherit_doc TreeSet.getGE!]
def getGE! [Inhabited α] (t : Raw α cmp) (k : α) : α :=
  TreeMap.Raw.getKeyGE! t.inner k

@[inline, inherit_doc TreeSet.getGT!]
def getGT! [Inhabited α] (t : Raw α cmp) (k : α) : α :=
  TreeMap.Raw.getKeyGT! t.inner k

@[inline, inherit_doc TreeSet.getLE!]
def getLE! [Inhabited α] (t : Raw α cmp) (k : α) : α :=
  TreeMap.Raw.getKeyLE! t.inner k

@[inline, inherit_doc TreeSet.getLT!]
def getLT! [Inhabited α] (t : Raw α cmp) (k : α) : α :=
  TreeMap.Raw.getKeyLT! t.inner k

@[inline, inherit_doc TreeSet.getGED]
def getGED (t : Raw α cmp) (k : α) (fallback : α) : α :=
  TreeMap.Raw.getKeyGED t.inner k fallback

@[inline, inherit_doc TreeSet.getGTD]
def getGTD (t : Raw α cmp) (k : α) (fallback : α) : α :=
  TreeMap.Raw.getKeyGTD t.inner k fallback

@[inline, inherit_doc TreeSet.getLED]
def getLED (t : Raw α cmp) (k : α) (fallback : α) : α :=
  TreeMap.Raw.getKeyLED t.inner k fallback

@[inline, inherit_doc TreeSet.getLTD]
def getLTD (t : Raw α cmp) (k : α) (fallback : α) : α :=
  TreeMap.Raw.getKeyLTD t.inner k fallback

variable {δ : Type w} {m : Type w → Type w₂} [Monad m]

@[inline, inherit_doc TreeSet.empty]
def filter (f : α → Bool) (t : Raw α cmp) : Raw α cmp :=
  ⟨t.inner.filter fun a _ => f a⟩

@[inline, inherit_doc TreeSet.empty]
def foldlM (f : δ → (a : α) → m δ) (init : δ) (t : Raw α cmp) : m δ :=
  t.inner.foldlM (fun c a _ => f c a) init

@[inline, inherit_doc foldlM, deprecated foldlM (since := "2025-02-12")]
def foldM (f : δ → (a : α) → m δ) (init : δ) (t : Raw α cmp) : m δ :=
  t.foldlM f init

@[inline, inherit_doc TreeSet.empty]
def foldl (f : δ → (a : α) → δ) (init : δ) (t : Raw α cmp) : δ :=
  t.inner.foldl (fun c a _ => f c a) init

@[inline, inherit_doc foldl, deprecated foldl (since := "2025-02-12")]
def fold (f : δ → (a : α) → δ) (init : δ) (t : Raw α cmp) : δ :=
  t.foldl f init

@[inline, inherit_doc TreeSet.empty]
def foldrM (f : (a : α) → δ → m δ) (init : δ) (t : Raw α cmp) : m δ :=
  t.inner.foldrM (fun a _ acc => f a acc) init

@[inline, inherit_doc TreeSet.empty]
def foldr (f : (a : α) → δ → δ) (init : δ) (t : Raw α cmp) : δ :=
  t.inner.foldr (fun a _ acc => f a acc) init

@[inline, inherit_doc foldr, deprecated foldr (since := "2025-02-12")]
def revFold (f : δ → (a : α) → δ) (init : δ) (t : Raw α cmp) : δ :=
  foldr (fun a acc => f acc a) init t

@[inline, inherit_doc TreeSet.partition]
def partition (f : (a : α) → Bool) (t : Raw α cmp) : Raw α cmp × Raw α cmp :=
  let p := t.inner.partition fun a _ => f a; (⟨p.1⟩, ⟨p.2⟩)

@[inline, inherit_doc TreeSet.empty]
def forM (f : α → m PUnit) (t : Raw α cmp) : m PUnit :=
  t.inner.forM (fun a _ => f a)

@[inline, inherit_doc TreeSet.empty]
def forIn (f : α → δ → m (ForInStep δ)) (init : δ) (t : Raw α cmp) : m δ :=
  t.inner.forIn (fun a _ c => f a c) init

instance : ForM m (Raw α cmp) α where
  forM t f := t.forM f

instance {t : Type w → Type w} : ForIn t (Raw α cmp) α where
  forIn t init f := t.forIn (fun a acc => f a acc) init

@[inline, inherit_doc TreeSet.empty]
def any (t : Raw α cmp) (p : α → Bool) : Bool :=
  t.inner.any (fun a _ => p a)

@[inline, inherit_doc TreeSet.empty]
def all (t : Raw α cmp) (p : α → Bool) : Bool :=
  t.inner.all (fun a _ => p a)

@[inline, inherit_doc TreeSet.empty]
def toList (t : Raw α cmp) : List α :=
  t.inner.inner.inner.foldr (fun a _ l => a :: l) ∅

@[inline, inherit_doc TreeSet.ofList]
def ofList (l : List α) (cmp : α → α → Ordering := by exact compare) : Raw α cmp :=
  ⟨TreeMap.Raw.unitOfList l cmp⟩

@[inline, inherit_doc ofList, deprecated ofList (since := "2025-02-12")]
def fromList (l : List α) (cmp : α → α → Ordering) : Raw α cmp :=
  ofList l cmp

@[inline, inherit_doc TreeSet.empty]
def toArray (t : Raw α cmp) : Array α :=
  t.foldl (init := #[]) fun acc k => acc.push k

@[inline, inherit_doc TreeSet.ofArray]
def ofArray (a : Array α) (cmp : α → α → Ordering := by exact compare) : Raw α cmp :=
  ⟨TreeMap.Raw.unitOfArray a cmp⟩

@[inline, inherit_doc ofArray, deprecated ofArray (since := "2025-02-12")]
def fromArray (a : Array α) (cmp : α → α → Ordering) : Raw α cmp :=
  ofArray a cmp

@[inline, inherit_doc TreeSet.empty]
def merge (t₁ t₂ : Raw α cmp) : Raw α cmp :=
  ⟨TreeMap.Raw.mergeWith (fun _ _ _ => ()) t₁.inner t₂.inner⟩

@[inline, inherit_doc TreeSet.insertMany]
def insertMany {ρ} [ForIn Id ρ α] (t : Raw α cmp) (l : ρ) : Raw α cmp :=
  ⟨TreeMap.Raw.insertManyIfNewUnit t.inner l⟩

@[inline, inherit_doc TreeSet.empty]
def eraseMany {ρ} [ForIn Id ρ α] (t : Raw α cmp) (l : ρ) : Raw α cmp :=
  ⟨t.inner.eraseMany l⟩

instance [Repr α] : Repr (Raw α cmp) where
  reprPrec m prec := Repr.addAppParen ("TreeSet.Raw.ofList " ++ repr m.toList) prec

end Raw

end TreeSet

end Std
