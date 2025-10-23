/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers.Monadic.Partial
public import Init.Data.Iterators.Consumers.Monadic.Total
public import Init.Data.Iterators.Internal.LawfulMonadLiftFunction
public import Init.Internal.ExtrinsicTermination

@[expose] public section

/-!
# Collectors

This module provides consumers that collect the values emitted by an iterator in a data structure.
Concretely, the following operations are provided:

* `IterM.toList`, collecting the values in a list
* `IterM.toListRev`, collecting the values in a list in reverse order but more efficiently
* `IterM.toArray`, collecting the values in an array

Some producers and combinators provide specialized implementations. These are captured by the
`IteratorCollect` type class. They should be implemented by all types of iterators. A default
implementation is provided. The typeclass `LawfulIteratorCollect` asserts that an `IteratorCollect`
instance equals the default implementation.
-/

namespace Std.Iterators
open Std.Internal

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
  toArrayMapped :
    (lift : ⦃δ : Type w⦄ → m δ → n δ) → {γ : Type w} → (β → n γ) → IterM (α := α) m β → n (Array γ)

end Typeclasses

section ToArray

/--
This is an internal function used in `IteratorCollect.defaultImplementation`.

It iterates over an iterator and applies `f` whenever a value is emitted before inserting the result
of `f` into an array.
-/
@[always_inline, no_expose]
def IterM.DefaultConsumers.toArrayMapped {α β : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Monad n] [Iterator α m β]
    (lift : ⦃α : Type w⦄ → m α → n α) {γ : Type w} (f : β → n γ)
    (it : IterM (α := α) m β) : n (Array γ) :=
  letI : MonadLift m n := ⟨lift (α := _)⟩
  go it #[]
where
  @[always_inline]
  go it (acc : Array γ) : n (Array γ) :=
    letI : MonadLift m n := ⟨lift (α := _)⟩
    extrinsicFix₂ (C₂ := fun _ _ => n (Array γ)) (fun it acc recur => do
      match (← it.step).inflate.val with
      | .yield it' out => recur it' (acc.push (← f out))
      | .skip it' => recur it' acc
      | .done => return acc) it acc

/--
This is the default implementation of the `IteratorLoop` class.
It simply iterates through the iterator using `IterM.step`, incrementally building up the desired
data structure. For certain iterators, more efficient implementations are possible and should be
used instead.
-/
@[always_inline]
def IteratorCollect.defaultImplementation {α β : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Monad n] [Iterator α m β] :
    IteratorCollect α m n where
  toArrayMapped := IterM.DefaultConsumers.toArrayMapped

/--
Asserts that a given `IteratorCollect` instance is equal to `IteratorCollect.defaultImplementation`
*if the underlying iterator is finite*.
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

instance (α β : Type w) (m : Type w → Type w') (n : Type w → Type w'') [Monad n]
    [Iterator α m β] [Monad m] [Iterator α m β] [Finite α m] :
    haveI : IteratorCollect α m n := .defaultImplementation
    LawfulIteratorCollect α m n :=
  letI : IteratorCollect α m n := .defaultImplementation
  ⟨fun _ => rfl⟩

/--
Traverses the given iterator and stores the emitted values in an array.

If the iterator is not finite, this function might run forever. The variant
`it.ensureTermination.toArray` always terminates after finitely many steps.
-/
@[always_inline, inline]
def IterM.toArray {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    [IteratorCollect α m m] (it : IterM (α := α) m β) : m (Array β) :=
  IteratorCollect.toArrayMapped (fun ⦃_⦄ => id) pure it

/--
Traverses the given iterator and stores the emitted values in an array.

This function is deprecated. Instead of `it.allowNontermination.toArray`, use `it.toArray`.
-/
@[always_inline, inline, deprecated IterM.toArray (since := "2025-10-23")]
def IterM.Partial.toArray {α : Type w} {m : Type w → Type w'} {β : Type w} [Monad m]
    [Iterator α m β] (it : IterM.Partial (α := α) m β) [IteratorCollect α m m] : m (Array β) :=
  it.it.toArray

/--
Traverses the given iterator and stores the emitted values in an array.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using `IterM.toArray`.
-/
@[always_inline, inline]
def IterM.Total.toArray {α : Type w} {m : Type w → Type w'} {β : Type w} [Monad m]
    [Iterator α m β] [Finite α m] (it : IterM.Total (α := α) m β) [IteratorCollect α m m] :
    m (Array β) :=
  it.it.toArray

end ToArray

/--
Traverses the given iterator and stores the emitted values in reverse order in a list. Because
lists are prepend-only, this `toListRev` is usually more efficient that `toList`.

If the iterator is not finite, this function might run forever. The variant
`it.ensureTermination.toListRev` always terminates after finitely many steps.
-/
@[always_inline, inline]
def IterM.toListRev {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] (it : IterM (α := α) m β) : m (List β) :=
  go it []
where
  @[always_inline, inline]
  go (it : IterM m β) acc :=
    extrinsicFix₂ (fun it acc recur => do
      match (← it.step).inflate with
      | .yield it' out _ => recur it' (out :: acc)
      | .skip it' _ => recur it' acc
      | .done _ => return acc) it acc

/--
Traverses the given iterator and stores the emitted values in reverse order in a list. Because
lists are prepend-only, this `toListRev` is usually more efficient that `toList`.

This function is deprecated. Instead of `it.allowNontermination.toListRev`, use `it.toListRev`.
-/
@[always_inline, inline, deprecated IterM.toListRev (since := "2025-10-23")]
partial def IterM.Partial.toListRev {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] (it : IterM.Partial (α := α) m β) : m (List β) :=
  it.it.toListRev

/--
Traverses the given iterator and stores the emitted values in reverse order in a list. Because
lists are prepend-only, this `toListRev` is usually more efficient that `toList`.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using `IterM.toListRev`.
-/
@[always_inline, inline]
def IterM.Total.toListRev {α : Type w} {m : Type w → Type w'} {β : Type w} [Monad m]
    [Iterator α m β] [Finite α m] (it : IterM.Total (α := α) m β) :
    m (List β) :=
  it.it.toListRev

/--
Traverses the given iterator and stores the emitted values in a list. Because
lists are prepend-only, `toListRev` is usually more efficient that `toList`.

If the iterator is not finite, this function might run forever. The variant
`it.ensureTermination.toList` always terminates after finitely many steps.
-/
@[always_inline, inline]
def IterM.toList {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] [IteratorCollect α m m] (it : IterM (α := α) m β) : m (List β) :=
  Array.toList <$> IterM.toArray it

/--
Traverses the given iterator and stores the emitted values in a list. Because
lists are prepend-only, `toListRev` is usually more efficient that `toList`.

This function is deprecated. Instead of `it.allowNontermination.toList`, use `it.toList`.
-/
@[always_inline, inline, deprecated IterM.toList (since := "2025-10-23")]
def IterM.Partial.toList {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] (it : IterM.Partial (α := α) m β) [IteratorCollect α m m] :
    m (List β) :=
  Array.toList <$> it.it.toArray

/--
Traverses the given iterator and stores the emitted values in a list. Because
lists are prepend-only, `toListRev` is usually more efficient that `toList`.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using `IterM.toList`.
-/
@[always_inline, inline]
def IterM.Total.toList {α : Type w} {m : Type w → Type w'} {β : Type w} [Monad m]
    [Iterator α m β] [Finite α m] (it : IterM.Total (α := α) m β) [IteratorCollect α m m] :
    m (List β) :=
  it.it.toList

end Std.Iterators
