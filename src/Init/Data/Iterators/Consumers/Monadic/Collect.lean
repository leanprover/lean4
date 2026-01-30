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
public import Init.WFExtrinsicFix

set_option linter.missingDocs true

@[expose] public section

/-!
# Collectors

This module provides consumers that collect the values emitted by an iterator in a data structure.
Concretely, the following operations are provided:

* `IterM.toList`, collecting the values in a list
* `IterM.toListRev`, collecting the values in a list in reverse order but more efficiently
* `IterM.toArray`, collecting the values in an array
-/

namespace Std
open Std.Internal Std.Iterators

section ToArray

/--
If this relation is well-founded, then `IterM.toArray`, `IterM.toList` and `IterM.toListRev` are
guaranteed to finish after finitely many steps. If all of the iterator's steps terminate
individually, `IterM.toArray` is guaranteed to terminate.
-/
def IterM.toArray.RecursionRel {α β : Type w} {m : Type w → Type w'}
    [Iterator α m β] {γ : Type w} (x' x : (_ : IterM (α := α) m β) ×' Array γ) : Prop :=
  (∃ out, x.1.IsPlausibleStep (.yield x'.1 out) ∧ ∃ a, x'.2 = x.2.push a) ∨
    (x.1.IsPlausibleStep (.skip x'.1) ∧ x'.2 = x.2)

/--
Traverses the given iterator and stores the emitted values in an array.

If the iterator is not finite, this function might run forever. The variant
`it.ensureTermination.toArray` always terminates after finitely many steps.
-/
@[always_inline, inline]
def IterM.toArray {α β : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β]
    (it : IterM (α := α) m β) : m (Array β) :=
  go it #[]
where
  @[always_inline]
  go it (acc : Array β) : m (Array β) :=
    WellFounded.extrinsicFix₂ (C₂ := fun _ _ => m (Array β)) (InvImage TerminationMeasures.Finite.Rel (·.1.finitelyManySteps!))
    (fun (it : IterM (α := α) m β) acc recur => do
      match (← it.step).inflate with
      | .yield it' out h =>
        recur it' (acc.push out) (by exact TerminationMeasures.Finite.rel_of_yield ‹_›)
      | .skip it' h => recur it' acc (by exact TerminationMeasures.Finite.rel_of_skip ‹_›)
      | .done _ => return acc) it acc

/--
Traverses the given iterator and stores the emitted values in an array.

This function is deprecated. Instead of `it.allowNontermination.toArray`, use `it.toArray`.
-/
@[always_inline, inline, deprecated IterM.toArray (since := "2025-10-23")]
def IterM.Partial.toArray {α : Type w} {m : Type w → Type w'} {β : Type w} [Monad m]
    [Iterator α m β] (it : IterM.Partial (α := α) m β) : m (Array β) :=
  it.it.toArray

/--
Traverses the given iterator and stores the emitted values in an array.

This variant terminates after finitely many steps and requires a proof that the iterator is
finite. If such a proof is not available, consider using `IterM.toArray`.
-/
@[always_inline, inline]
def IterM.Total.toArray {α : Type w} {m : Type w → Type w'} {β : Type w} [Monad m]
    [Iterator α m β] [Finite α m] (it : IterM.Total (α := α) m β) :
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
    WellFounded.extrinsicFix₂ (InvImage TerminationMeasures.Finite.Rel (·.1.finitelyManySteps!))
      (fun it acc recur => do
        match (← it.step).inflate with
        | .yield it' out h => recur it' (out :: acc) (TerminationMeasures.Finite.rel_of_yield h)
        | .skip it' h => recur it' acc (TerminationMeasures.Finite.rel_of_skip h)
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
    [Iterator α m β] (it : IterM (α := α) m β) : m (List β) :=
  Array.toList <$> IterM.toArray it

/--
Traverses the given iterator and stores the emitted values in a list. Because
lists are prepend-only, `toListRev` is usually more efficient that `toList`.

This function is deprecated. Instead of `it.allowNontermination.toList`, use `it.toList`.
-/
@[always_inline, inline, deprecated IterM.toList (since := "2025-10-23")]
def IterM.Partial.toList {α : Type w} {m : Type w → Type w'} [Monad m] {β : Type w}
    [Iterator α m β] (it : IterM.Partial (α := α) m β) :
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
    [Iterator α m β] [Finite α m] (it : IterM.Total (α := α) m β) :
    m (List β) :=
  it.it.toList

end Std
