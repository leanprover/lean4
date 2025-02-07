/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Std.Data.TreeMap.Basic
import Std.Data.TreeSet.Raw

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

universe u v

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
structure TreeSet (α : Type u) (cmp : α → α → Ordering) where
  /-- Internal implementation detail of the tree map. -/
  inner : TreeMap α Unit cmp

namespace TreeSet

@[inline, inherit_doc Raw.empty]
def empty : TreeSet α cmp :=
  ⟨TreeMap.empty⟩

instance : EmptyCollection (TreeSet α cmp) where
  emptyCollection := empty

instance : Inhabited (TreeSet α cmp) where
  default := ∅

@[inline, inherit_doc Raw.insert]
def insert (l : TreeSet α cmp) (a : α) : TreeSet α cmp :=
  ⟨l.inner.insertIfNew a ()⟩

instance : Singleton α (TreeSet α cmp) where
  singleton e := empty.insert e

instance : Insert α (TreeSet α cmp) where
  insert e s := s.insert e

instance : LawfulSingleton α (TreeSet α cmp) where
  insert_emptyc_eq _ := rfl

@[inline, inherit_doc Raw.containsThenInsert]
def containsThenInsert (t : TreeSet α cmp) (a : α) : Bool × TreeSet α cmp :=
  letI : Ord α := ⟨cmp⟩
  let p := t.inner.containsThenInsertIfNew a ()
  (p.1, ⟨p.2⟩)

@[inline, inherit_doc Raw.contains]
def contains (l : TreeSet α cmp) (a : α) : Bool :=
  l.inner.contains a

instance : Membership α (TreeSet α cmp) where
  mem m a := m.contains a

instance {m : TreeSet α cmp} {a : α} : Decidable (a ∈ m) :=
  inferInstanceAs <| Decidable (m.contains a)

@[inline, inherit_doc Raw.size]
def size (t : TreeSet α cmp) : Nat :=
  t.inner.size

@[inline, inherit_doc Raw.isEmpty]
def isEmpty (t : TreeSet α cmp) : Bool :=
  t.inner.isEmpty

@[inline, inherit_doc Raw.isSingleton]
def isSingleton (t : TreeSet α cmp) : Bool :=
  t.inner.isSingleton

@[inline, inherit_doc Raw.erase]
def erase (t : TreeSet α cmp) (a : α) : TreeSet α cmp :=
  ⟨t.inner.erase a⟩

universe w w₂
variable  {γ δ: Type w} {m : Type w → Type w₂} [Monad m]

@[inline, inherit_doc Raw.filter]
def filter (f : α → Bool) (m : TreeSet α cmp) : TreeSet α cmp :=
  ⟨m.inner.filter fun a _ => f a⟩

@[inline, inherit_doc Raw.foldlM]
def foldlM {m δ} [Monad m] (f : δ → (a : α) → m δ) (init : δ) (t : TreeSet α cmp) : m δ :=
  t.inner.foldlM (fun c a _ => f c a) init

@[inline, inherit_doc Raw.foldl]
def foldl (f : δ → (a : α) → δ) (init : δ) (t : TreeSet α cmp) : δ :=
  t.inner.foldl (fun c a _ => f c a) init

@[inline, inherit_doc Raw.forM]
def forM (f : α → m PUnit) (t : TreeSet α cmp) : m PUnit :=
  t.inner.forM (fun a _ => f a)

@[inline, inherit_doc Raw.forIn]
def forIn (f : α → δ → m (ForInStep δ)) (init : δ) (t : TreeSet α cmp) : m δ :=
  t.inner.forIn (fun a _ c => f a c) init

instance : ForM m (TreeSet α cmp) α where
  forM t f := t.forM f

instance : ForIn m (TreeSet α cmp) α where
  forIn m init f := m.forIn (fun a acc => f a acc) init

@[inline, inherit_doc Raw.any]
def any (t : TreeSet α cmp) (p : α → Bool) : Bool :=
  t.inner.any (fun a _ => p a)

@[inline, inherit_doc Raw.all]
def all (t : TreeSet α cmp) (p : α → Bool) : Bool :=
  t.inner.all (fun a _ => p a)

@[inline, inherit_doc Raw.toList]
def toList (t : TreeSet α cmp) : List α :=
  t.inner.inner.inner.foldr (fun l a _ => a :: l) ∅

@[inline, inherit_doc Raw.ofList]
def ofList (l : List α) (cmp : α → α → Ordering) : TreeSet α cmp :=
  l.foldl (fun r a => r.insert a) ∅

@[inline, inherit_doc Raw.ofList, deprecated ofList (since := "2025-02-06")]
def fromList (l : List α) (cmp : α → α → Ordering) : TreeSet α cmp :=
  ofList l cmp

@[inline, inherit_doc Raw.toArray]
def toArray (t : TreeSet α cmp) : Array α :=
  t.foldl (init := ∅) fun acc k => acc.push k

@[inline, inherit_doc Raw.ofArray]
def ofArray (l : Array α) (cmp : α → α → Ordering) : TreeSet α cmp :=
  l.foldl (init := ∅) (fun t a => t.insert a)

@[inline, inherit_doc Raw.merge]
def merge (t₁ t₂ : TreeSet α cmp) : TreeSet α cmp :=
  ⟨TreeMap.mergeBy (fun _ _ _ => ()) t₁.inner t₂.inner⟩

@[inline, inherit_doc Raw.eraseMany]
def eraseMany {ρ} [ForIn Id ρ α] (t : TreeSet α cmp) (l : ρ) : TreeSet α cmp :=
  ⟨t.inner.eraseMany l⟩

instance [Repr α] : Repr (TreeSet α cmp) where
  reprPrec m prec := Repr.addAppParen ("TreeSet.ofList " ++ repr m.toList) prec

end TreeSet

end Std
