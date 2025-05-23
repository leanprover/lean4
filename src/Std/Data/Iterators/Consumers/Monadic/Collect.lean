/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Consumers.Monadic.Partial

/-!
# Collectors

This module provides consumers that collect the values emitted by an iterator in a data structure.
Concretely, the following operations are provided:

* `IterM.toList`, collecting the values in a list
* `IterM.toListRev`, collecting the values in a list in reverse order but more efficiently
* `IterM.toArray`, collecting the values in an array

Some producers and combinators provide specialized implementations. These are captured by the
`IteratorCollect` and `IteratorCollectPartial` typeclasses. They should be implemented by all
types of iterators. A default implementation is provided. The typeclass `LawfulIteratorCollect`
asserts that an `IteratorCollect` instance equals the default implementation.
-/

namespace Std.Iterators

section Typeclasses

/--
`IteratorCollect α m` provides efficient implementations of collectors for `α`-based
iterators. Right now, it is limited to a potentially optimized `toArray` implementation.

This class is experimental and users of the iterator API should not explicitly depend on it.
They can, however, assume that consumers that require an instance will work for all iterators
provided by the standard library.
-/
class IteratorCollect (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β] where
  toArrayMapped [Finite α m] : ∀ {γ : Type w}, (β → m γ) → IterM (α := α) m β → m (Array γ)

/--
`IteratorCollectPartial α m` provides efficient implementations of collectors for `α`-based
iterators. Right now, it is limited to a potentially optimized partial `toArray` implementation.

This class is experimental and users of the iterator API should not explicitly depend on it.
They can, however, assume that consumers that require an instance will work for all iterators
provided by the standard library.
-/
class IteratorCollectPartial
  (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β] where
    toArrayMappedPartial : ∀ {γ : Type w}, (β → m γ) → IterM (α := α) m β → m (Array γ)

end Typeclasses

section ToArray

/--
This is an internal function used in `IteratorCollect.defaultImplementation`.

It iterates over an iterator and applies `f` whenever a value is emitted before inserting the result
of `f` into an array.
-/
@[always_inline, inline]
def IterM.DefaultConsumers.toArrayMapped {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] [Finite α m] {γ : Type w} (f : β → m γ) (it : IterM (α := α) m β) : m (Array γ) :=
  go it #[]
where
  @[specialize]
  go [Monad m] [Finite α m] (it : IterM (α := α) m β) a := do
    match ← it.step with
    | .yield it' b _ => go it' (a.push (← f b))
    | .skip it' _ => go it' a
    | .done _ => return a
  termination_by it.finitelyManySteps

/--
This is the default implementation of the `IteratorLoop` class.
It simply iterates through the iterator using `IterM.step`, incrementally building up the desired
data structure. For certain iterators, more efficient implementations are possible and should be
used instead.
-/
@[always_inline, inline]
def IteratorCollect.defaultImplementation {α : Type w} {m : Type w → Type w'}
    [Monad m] [Iterator α m β] : IteratorCollect α m where
  toArrayMapped := IterM.DefaultConsumers.toArrayMapped

/--
Asserts that a given `IteratorCollect` instance is equal to `IteratorCollect.defaultImplementation`.
(Even though equal, the given instance might be vastly more efficient.)
-/
class LawfulIteratorCollect (α : Type w) (m : Type w → Type w') [Monad m] [Iterator α m β]
    [i : IteratorCollect α m] where
  lawful : i = .defaultImplementation

theorem LawfulIteratorCollect.toArrayMapped_eq {α β γ : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [Finite α m] [IteratorCollect α m] [hl : LawfulIteratorCollect α m]
    {f : β → m γ} {it : IterM (α := α) m β} :
    IteratorCollect.toArrayMapped f it = IterM.DefaultConsumers.toArrayMapped f it := by
  cases hl.lawful; rfl

instance (α : Type w) (m : Type w → Type w') [Monad m] [Iterator α m β]
    [Monad m] [Iterator α m β] [Finite α m] :
    haveI : IteratorCollect α m := .defaultImplementation
    LawfulIteratorCollect α m :=
  letI : IteratorCollect α m := .defaultImplementation
  ⟨rfl⟩

/--
This is an internal function used in `IteratorCollectPartial.defaultImplementation`.

It iterates over an iterator and applies `f` whenever a value is emitted before inserting the result
of `f` into an array.
-/
@[always_inline, inline]
partial def IterM.DefaultConsumers.toArrayMappedPartial {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] {γ : Type w} (f : β → m γ) (it : IterM (α := α) m β) : m (Array γ) :=
  go it #[]
where
  @[specialize]
  go [Monad m] (it : IterM (α := α) m β) a := do
    match ← it.step with
    | .yield it' b _ => go it' (a.push (← f b))
    | .skip it' _ => go it' a
    | .done _ => return a

/--
This is the default implementation of the `IteratorLoopPartial` class.
It simply iterates through the iterator using `IterM.step`, incrementally building up the desired
data structure. For certain iterators, more efficient implementations are possible and should be
used instead.
-/
@[always_inline, inline]
def IteratorCollectPartial.defaultImplementation {α : Type w} {m : Type w → Type w'}
    [Monad m] [Iterator α m β] : IteratorCollectPartial α m where
  toArrayMappedPartial := IterM.DefaultConsumers.toArrayMappedPartial

/--
Traverses the given iterator and stores the emitted values in an array.

This function requires a `Finite` instance proving that the iterator will finish after a finite
number of steps. If the iterator is not finite or such an instance is not available, consider using
`it.allowNontermination.toArray` instead of `it.toArray`. However, it is not possible to formally
verify the behavior of the partial variant.
-/
@[always_inline, inline]
def IterM.toArray {α : Type w} {m : Type w → Type w'} {β : Type w} [Monad m]
    [Iterator α m β] [Finite α m] [IteratorCollect α m] (it : IterM (α := α) m β) : m (Array β) :=
  IteratorCollect.toArrayMapped pure it

/--
Traverses the given iterator and stores the emitted values in an array.

This is a partial, potentially nonterminating, function. It is not possible to formally verify
its behavior. If the iterator has a `Finite` instance, consider using `IterM.toArray` instead.
-/
@[always_inline, inline]
def IterM.Partial.toArray {α : Type w} {m : Type w → Type w'} {β : Type w} [Monad m]
    [Iterator α m β] (it : IterM.Partial (α := α) m β) [IteratorCollectPartial α m] : m (Array β) :=
  IteratorCollectPartial.toArrayMappedPartial pure it.it

end ToArray

/--
Traverses the given iterator and stores the emitted values in reverse order in a list. Because
lists are prepend-only, this `toListRev` is usually more efficient that `toList`.

This function requires a `Finite` instance proving that the iterator will finish after a finite
number of steps. If the iterator is not finite or such an instance is not available, consider using
`it.allowNontermination.toListRev` instead of `it.toListRev`. However, it is not possible to
formally verify the behavior of the partial variant.
-/
@[inline]
def IterM.toListRev {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] [Finite α m] (it : IterM (α := α) m β) : m (List β) :=
  go it []
where
  go [Finite α m] it bs := do
    match ← it.step with
    | .yield it' b _ => go it' (b :: bs)
    | .skip it' _ => go it' bs
    | .done _ => return bs
  termination_by it.finitelyManySteps

/--
Traverses the given iterator and stores the emitted values in reverse order in a list. Because
lists are prepend-only, this `toListRev` is usually more efficient that `toList`.

This is a partial, potentially nonterminating, function. It is not possible to formally verify
its behavior. If the iterator has a `Finite` instance, consider using `IterM.toListRev` instead.
-/
@[always_inline, inline]
partial def IterM.Partial.toListRev {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] (it : IterM.Partial (α := α) m β) : m (List β) :=
  go it.it []
where
  @[specialize]
  go it bs := do
    match ← it.step with
    | .yield it' b _ => go it' (b :: bs)
    | .skip it' _ => go it' bs
    | .done _ => return bs

/--
Traverses the given iterator and stores the emitted values in a list. Because
lists are prepend-only, `toListRev` is usually more efficient that `toList`.

This function requires a `Finite` instance proving that the iterator will finish after a finite
number of steps. If the iterator is not finite or such an instance is not available, consider using
`it.allowNontermination.toList` instead of `it.toList`. However, it is not possible to
formally verify the behavior of the partial variant.
-/
@[always_inline, inline]
def IterM.toList {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] [Finite α m] [IteratorCollect α m] (it : IterM (α := α) m β) : m (List β) :=
  Array.toList <$> IterM.toArray it

/--
Traverses the given iterator and stores the emitted values in a list. Because
lists are prepend-only, `toListRev` is usually more efficient that `toList`.

This is a partial, potentially nonterminating, function. It is not possible to formally verify
its behavior. If the iterator has a `Finite` instance, consider using `IterM.toList` instead.
-/
@[always_inline, inline]
def IterM.Partial.toList {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] (it : IterM.Partial (α := α) m β) [IteratorCollectPartial α m] : m (List β) :=
  Array.toList <$> it.toArray

end Std.Iterators
