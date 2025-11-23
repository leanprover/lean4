/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
module

prelude
public import Std.Data.DHashMap.Internal.AssocList.Basic

public section

/-!
# Definition of `DHashMap.Raw`

This file defines the type `Std.Data.DHashMap.Raw`. All of its functions are defined in the module
`Std.Data.DHashMap.Basic`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w w'

namespace Std.DHashMap

open Internal

/--
Dependent hash maps without a bundled well-formedness invariant, suitable for use in nested
inductive types. The well-formedness invariant is called `Raw.WF`. When in doubt, prefer `DHashMap`
over `DHashMap.Raw`. Lemmas about the operations on `Std.Data.DHashMap.Raw` are available in the
module `Std.Data.DHashMap.RawLemmas`.

The hash table is backed by an `Array`. Users should make sure that the hash map is used linearly to
avoid expensive copies.

This is a simple separate-chaining hash table. The data of the hash map consists of a cached size
and an array of buckets, where each bucket is a linked list of key-value pairs. The number of buckets
is always a power of two. The hash map doubles its size upon inserting an element such that the
number of elements is more than 75% of the number of buckets.

The hash map uses `==` (provided by the `BEq` typeclass) to compare keys and `hash` (provided by
the `Hashable` typeclass) to hash them. To ensure that the operations behave as expected, `==`
should be an equivalence relation and `a == b` should imply `hash a = hash b` (see also the
`EquivBEq` and `LawfulHashable` typeclasses). Both of these conditions are automatic if the BEq
instance is lawful, i.e., if `a == b` implies `a = b`.
-/
structure Raw (α : Type u) (β : α → Type v) where
  /-- The number of mappings present in the hash map -/
  size : Nat
  /-- Internal implementation detail of the hash map -/
  buckets : Array (DHashMap.Internal.AssocList α β)

namespace Raw

variable {α : Type u} {β : α → Type v} {δ : Type w} {m : Type w → Type w'}

/--
Monadically computes a value by folding the given function over the mappings in the hash
map in some order.
-/
@[inline] def foldM [Monad m] (f : δ → (a : α) → β a → m δ) (init : δ) (b : Raw α β) : m δ :=
  b.buckets.foldlM (fun acc l => l.foldlM f acc) init

/-- Folds the given function over the mappings in the hash map in some order. -/
@[inline] def fold (f : δ → (a : α) → β a → δ) (init : δ) (b : Raw α β) : δ :=
  Id.run (b.foldM (pure <| f · · ·) init)

/-- Carries out a monadic action on each mapping in the hash map in some order. -/
@[inline] def forM [Monad m] (f : (a : α) → β a → m PUnit) (b : Raw α β) : m PUnit :=
  b.buckets.forM (AssocList.forM f)

/-- Support for the `for` loop construct in `do` blocks. -/
@[inline] def forIn [Monad m] (f : (a : α) → β a → δ → m (ForInStep δ)) (init : δ) (b : Raw α β) : m δ :=
  ForIn.forIn b.buckets init (fun bucket acc => bucket.forInStep acc f)

instance x : ForM m (Raw α β) ((a : α) × β a) where
  forM m f := m.forM (fun a b => f ⟨a, b⟩)

instance : ForIn m (Raw α β) ((a : α) × β a) where
  forIn m init f := m.forIn (fun a b acc => f ⟨a, b⟩ acc) init

end Raw

end Std.DHashMap
