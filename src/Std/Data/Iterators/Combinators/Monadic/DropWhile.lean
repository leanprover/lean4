/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Nat.Lemmas
public import Init.Data.Iterators.Consumers.Monadic.Collect
public import Init.Data.Iterators.Consumers.Monadic.Loop
public import Init.Data.Iterators.Internal.Termination
public import Init.Data.Iterators.PostconditionMonad
import Init.Control.Lawful.MonadAttach.Lemmas

@[expose] public section

/-!
# Monadic `dropWhile` iterator combinator

This module provides the iterator combinator `IterM.dropWhile` that will drop all values emitted
by a given iterator until a given predicate on these values becomes false the first time. Beginning
with that moment, the combinator will forward all emitted values.

Several variants of this combinator are provided:

* `M` suffix: Instead of a pure function, this variant takes a monadic function. Given a suitable
  `MonadLiftT` instance, it will also allow lifting the iterator to another monad first and then
  applying the mapping function in this monad.
* `WithPostcondition` suffix: This variant takes a monadic function where the return type in the
  monad is a subtype. This variant is in rare cases necessary for the intrinsic verification of an
  iterator, and particularly for specialized termination proofs. If possible, avoid this.
-/

namespace Std.Iterators

variable {α : Type w} {m : Type w → Type w'} {β : Type w}

/--
Internal state of the `dropWhile` combinator. Do not depend on its internals.
-/
@[unbox]
structure DropWhile (α : Type w) (m : Type w → Type w') (β : Type w)
    (P : β → m (ULift Bool)) where
  /-- Internal implementation detail of the iterator library. -/
  dropping : Bool
  /-- Internal implementation detail of the iterator library. -/
  inner : IterM (α := α) m β

/--
Constructs intermediate states of an iterator created with the combinator `IterM.dropWhileM`.
When `it.dropWhileM P` has stopped dropping elements, its new state cannot be created
directly with `IterM.dropWhileM` but only with `Intermediate.dropWhileM`.

`Intermediate.dropWhileM` is meant to be used only for internally or for verification purposes.
-/
@[always_inline, inline]
def IterM.Intermediate.dropWhileM [Monad m] (P : β → m (ULift Bool)) (dropping : Bool)
    (it : IterM (α := α) m β) : IterM (α := DropWhile α m β P) m β :=
  toIterM ⟨dropping, it⟩ m β

/--
Constructs intermediate states of an iterator created with the combinator `IterM.dropWhile`.
When `it.dropWhile P` has stopped dropping elements, its new state cannot be created
directly with `IterM.dropWhile` but only with `Intermediate.dropWhile`.

`Intermediate.dropWhile` is meant to be used only for internally or for verification purposes.
-/
@[always_inline, inline]
def IterM.Intermediate.dropWhile [Monad m] (P : β → Bool) (dropping : Bool)
    (it : IterM (α := α) m β) :=
  (IterM.Intermediate.dropWhileM (pure ∘ ULift.up ∘ P) dropping it : IterM m β)

/--
Given an iterator `it` and a monadic predicate `P`, `it.dropWhileM P` is an iterator that
emits the values emitted by `it` starting from the first value that is rejected by `P`.
The elements before are dropped.

If `P` is pure, then the simpler variant `dropWhile` can be used instead.

**Marble diagram (ignoring monadic effects):**

Assuming that the predicate `P` accepts `a` and `b` but rejects `c`:

```text
it                ---a----b---c--d-e--⊥
it.dropWhileM P   ------------c--d-e--⊥

it                ---a----⊥
it.dropWhileM P   --------⊥
```

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is finite

Depending on `P`, it is possible that `it.dropWhileM P` is finite (or productive) although
`it` is not. In this case, the `Finite` (or `Productive`) instance needs to be proved manually.
Use `dropWhileWithPostcondition` if the termination behavior depends on `P`'s behavior.

**Performance:**

This combinator calls `P` on each output of `it` until the predicate evaluates to false. After
that, the combinator incurs an addictional O(1) cost for each value emitted by `it`.
-/
@[always_inline, inline]
def IterM.dropWhileM [Monad m] (P : β → m (ULift Bool)) (it : IterM (α := α) m β) :=
  (Intermediate.dropWhileM P true it : IterM m β)

/--
Given an iterator `it` and a predicate `P`, `it.dropWhile P` is an iterator that
emits the values emitted by `it` starting from the first value that is rejected by `P`.
The elements before are dropped.

In situations where `P` is monadic, use `dropWhileM` instead.

**Marble diagram (ignoring monadic effects):**

Assuming that the predicate `P` accepts `a` and `b` but rejects `c`:

```text
it               ---a----b---c--d-e--⊥
it.dropWhile P   ------------c--d-e--⊥

it               ---a----⊥
it.dropWhile P   --------⊥
```

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is finite

Depending on `P`, it is possible that `it.dropWhileM P` is productive although
`it` is not. In this case, the `Productive` instance needs to be proved manually.

**Performance:**

This combinator calls `P` on each output of `it` until the predicate evaluates to false. After
that, the combinator incurs an addictional O(1) cost for each value emitted by `it`.
-/
@[always_inline, inline]
def IterM.dropWhile [Monad m] (P : β → Bool) (it : IterM (α := α) m β) :=
  (Intermediate.dropWhile P true it : IterM m β)

@[always_inline, inline]
instance DropWhile.instIterator [Monad m] [Iterator α m β] {P} :
    Iterator (DropWhile α m β P) m β where
  step it := do
    match ← it.internalState.inner.step with
    | .yield it' out =>
      if it.internalState.dropping = true then
        match ← P out with
        | .up true => return .skip (IterM.Intermediate.dropWhileM P true it')
        | .up false => return .yield (IterM.Intermediate.dropWhileM P false it') out
      else return .yield (IterM.Intermediate.dropWhileM P false it') out
    | .skip it' => return .skip (IterM.Intermediate.dropWhileM P it.internalState.dropping it')
    | .done => return .done

private def DropWhile.instFinitenessRelation
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Iterator α m β] [Finite α m] {P} :
    FinitenessRelation (DropWhile α m β P) m where
  rel := InvImage WellFoundedRelation.rel
      (IterM.finitelyManySteps ∘ DropWhile.inner ∘ IterM.internalState)
  wf := by
    apply InvImage.wf
    exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, hs, h'⟩ := h
    obtain ⟨step', hs', h'⟩ := LawfulMonadAttach.canReturn_bind_imp' h'
    cases step', hs' using PlausibleIterStep.casesOn'
    · simp only at h'
      split at h'
      · obtain ⟨Px, hPx, h'⟩ := LawfulMonadAttach.canReturn_bind_imp' h'
        split at h'
        all_goals
          cases LawfulMonadAttach.eq_of_canReturn_pure h'
          cases hs
          apply IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
      · cases LawfulMonadAttach.eq_of_canReturn_pure h'
        cases hs
        exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
    · cases LawfulMonadAttach.eq_of_canReturn_pure h'
      cases hs
      exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›
    · cases LawfulMonadAttach.eq_of_canReturn_pure h'
      cases hs

instance DropWhile.instFinite
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Iterator α m β] [Finite α m] {P} :
    Finite (DropWhile α m β P) m :=
  by exact Finite.of_finitenessRelation instFinitenessRelation

instance DropWhile.instIteratorCollect [Monad m] [MonadAttach m] [Monad n]
    [Iterator α m β] [Productive α m] {P} :
    IteratorCollect (DropWhile α m β P) m n :=
  .defaultImplementation

instance DropWhile.instIteratorLoop [Monad m] [MonadAttach m] [Monad n] [MonadAttach n]
    [Iterator α m β] : IteratorLoop (DropWhile α m β P) m n :=
  .defaultImplementation

end Std.Iterators
