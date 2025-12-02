/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers.Monadic.Partial
public import Init.Data.Iterators.Internal.LawfulMonadLiftFunction

@[expose] public section

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

namespace Std
open Std.Internal Std.Iterators

section Typeclasses

/--
`IteratorCollect α m` provides efficient implementations of collectors for `α`-based
iterators. Right now, it is limited to a potentially optimized `toArray` implementation.

This class is experimental and users of the iterator API should not explicitly depend on it.
They can, however, assume that consumers that require an instance will work for all iterators
provided by the standard library.

Note: For this to be compositional enough to be useful, `toArrayMapped` would need to accept a
termination proof for the specific mapping function used instead of the blanket `Finite α m`
instance. Otherwise, most combinators like `map` cannot implement their own instance relying on
the instance of their base iterators. However, fixing this is currently low priority.
-/
class IteratorCollect (α : Type w) (m : Type w → Type w') (n : Type w → Type w'')
    {β : Type w} [Iterator α m β] where
  /--
  Maps the emitted values of an iterator using the given function and collects the results in an
  `Array`. This is an internal implementation detail. Consider using `it.map f |>.toArray` instead.
  -/
  toArrayMapped [Finite α m] :
    (lift : ⦃δ : Type w⦄ → m δ → n δ) → {γ : Type w} → (β → n γ) → IterM (α := α) m β → n (Array γ)

/--
`IteratorCollectPartial α m` provides efficient implementations of collectors for `α`-based
iterators. Right now, it is limited to a potentially optimized partial `toArray` implementation.

This class is experimental and users of the iterator API should not explicitly depend on it.
They can, however, assume that consumers that require an instance will work for all iterators
provided by the standard library.
-/
class IteratorCollectPartial (α : Type w) (m : Type w → Type w') (n : Type w → Type w'')
    {β : Type w} [Iterator α m β] where
  /--
  Maps the emitted values of an iterator using the given function and collects the results in an
  `Array`. This is an internal implementation detail.
  Consider using `it.map f |>.allowNontermination.toArray` instead.
  -/
  toArrayMappedPartial :
    (lift : ⦃δ : Type w⦄ → m δ → n δ) → {γ : Type w} → (β → n γ) → IterM (α := α) m β → n (Array γ)

end Typeclasses

section ToArray

/--
This is an internal function used in `IteratorCollect.defaultImplementation`.

It iterates over an iterator and applies `f` whenever a value is emitted before inserting the result
of `f` into an array.
-/
@[always_inline, inline]
def IterM.DefaultConsumers.toArrayMapped {α β : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Monad n] [Iterator α m β] [Finite α m]
    (lift : ⦃α : Type w⦄ → m α → n α) {γ : Type w} (f : β → n γ)
    (it : IterM (α := α) m β) : n (Array γ) :=
  go it #[]
where
  @[specialize]
  go [Monad n] [Finite α m] (it : IterM (α := α) m β) a := letI : MonadLift m n := ⟨lift (α := _)⟩; do
    match (← it.step).inflate with
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
def IteratorCollect.defaultImplementation {α β : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Monad n] [Iterator α m β] :
    IteratorCollect α m n where
  toArrayMapped := IterM.DefaultConsumers.toArrayMapped

/--
Asserts that a given `IteratorCollect` instance is equal to `IteratorCollect.defaultImplementation`.
(Even though equal, the given instance might be vastly more efficient.)
-/
class LawfulIteratorCollect (α : Type w) (m : Type w → Type w') (n : Type w → Type w'')
    {β : Type w} [Monad m] [Monad n] [Iterator α m β] [i : IteratorCollect α m n] where
  lawful_toArrayMapped : ∀ lift [LawfulMonadLiftFunction lift] [Finite α m],
    i.toArrayMapped lift (α := α) (γ := γ)
      = IteratorCollect.defaultImplementation.toArrayMapped lift

theorem LawfulIteratorCollect.toArrayMapped_eq {α β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Monad m] [Monad n] [Iterator α m β] [Finite α m] [IteratorCollect α m n]
    [hl : LawfulIteratorCollect α m n] {lift : ⦃δ : Type w⦄ → m δ → n δ}
    [LawfulMonadLiftFunction lift]
    {f : β → n γ} {it : IterM (α := α) m β} :
    IteratorCollect.toArrayMapped lift f it (m := m) =
      IterM.DefaultConsumers.toArrayMapped lift f it (m := m) := by
  rw [lawful_toArrayMapped]; rfl

instance instLawfulIteratorCollectDefaultImplementation (α β : Type w) (m : Type w → Type w')
    (n : Type w → Type w'') [Monad n] [Iterator α m β] [Monad m] [Iterator α m β] [Finite α m] :
    haveI : IteratorCollect α m n := .defaultImplementation
    LawfulIteratorCollect α m n :=
  letI : IteratorCollect α m n := .defaultImplementation
  ⟨fun _ => rfl⟩

/--
This is an internal function used in `IteratorCollectPartial.defaultImplementation`.

It iterates over an iterator and applies `f` whenever a value is emitted before inserting the result
of `f` into an array.
-/
@[always_inline, inline]
partial def IterM.DefaultConsumers.toArrayMappedPartial {α β : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Monad n] [Iterator α m β]
    (lift : {α : Type w} → m α → n α) {γ : Type w} (f : β → n γ)
    (it : IterM (α := α) m β) : n (Array γ) :=
  go it #[]
where
  @[specialize]
  go [Monad n] (it : IterM (α := α) m β) a := letI : MonadLift m n := ⟨lift⟩; do
    match (← it.step).inflate with
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
def IteratorCollectPartial.defaultImplementation {α β : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Monad n] [Iterator α m β] :
    IteratorCollectPartial α m n where
  toArrayMappedPartial := IterM.DefaultConsumers.toArrayMappedPartial

/--
Traverses the given iterator and stores the emitted values in an array.

This function requires a `Finite` instance proving that the iterator will finish after a finite
number of steps. If the iterator is not finite or such an instance is not available, consider using
`it.allowNontermination.toArray` instead of `it.toArray`. However, it is not possible to formally
verify the behavior of the partial variant.
-/
@[always_inline, inline]
def IterM.toArray {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [Finite α m] [IteratorCollect α m m]
    (it : IterM (α := α) m β) : m (Array β) :=
  IteratorCollect.toArrayMapped (fun ⦃_⦄ => id) pure it

/--
Traverses the given iterator and stores the emitted values in an array.

This is a partial, potentially nonterminating, function. It is not possible to formally verify
its behavior. If the iterator has a `Finite` instance, consider using `IterM.toArray` instead.
-/
@[always_inline, inline]
def IterM.Partial.toArray {α : Type w} {m : Type w → Type w'} {β : Type w} [Monad m]
    [Iterator α m β] (it : IterM.Partial (α := α) m β) [IteratorCollectPartial α m m] : m (Array β) :=
  IteratorCollectPartial.toArrayMappedPartial (fun ⦃_⦄ => id) pure it.it

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
    match (← it.step).inflate with
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
    match (← it.step).inflate with
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
    [Iterator α m β] [Finite α m] [IteratorCollect α m m] (it : IterM (α := α) m β) : m (List β) :=
  Array.toList <$> IterM.toArray it

/--
Traverses the given iterator and stores the emitted values in a list. Because
lists are prepend-only, `toListRev` is usually more efficient that `toList`.

This is a partial, potentially nonterminating, function. It is not possible to formally verify
its behavior. If the iterator has a `Finite` instance, consider using `IterM.toList` instead.
-/
@[always_inline, inline]
def IterM.Partial.toList {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] (it : IterM.Partial (α := α) m β) [IteratorCollectPartial α m m] :
    m (List β) :=
  Array.toList <$> it.toArray

end Std
