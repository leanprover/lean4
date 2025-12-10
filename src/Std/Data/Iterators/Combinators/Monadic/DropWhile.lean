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

namespace Std
open Std.Iterators

variable {α : Type w} {m : Type w → Type w'} {β : Type w}

/--
Internal state of the `dropWhile` combinator. Do not depend on its internals.
-/
@[unbox]
structure Iterators.Types.DropWhile (α : Type w) (m : Type w → Type w') (β : Type w)
    (P : β → PostconditionT m (ULift Bool)) where
  /-- Internal implementation detail of the iterator library. -/
  dropping : Bool
  /-- Internal implementation detail of the iterator library. -/
  inner : IterM (α := α) m β

/--
Constructs intermediate states of an iterator created with the combinator
`IterM.dropWhileWithPostcondition`.
When `it.dropWhileWithPostcondition P` has stopped dropping elements, its new state cannot be
created directly with `IterM.dropWhileWithPostcondition` but only with
`Intermediate.dropWhileWithPostcondition`.

`Intermediate.dropWhileWithPostcondition` is meant to be used only for internally or for
verification purposes.
-/
@[always_inline, inline]
def IterM.Intermediate.dropWhileWithPostcondition (P : β → PostconditionT m (ULift Bool))
    (dropping : Bool) (it : IterM (α := α) m β) :=
  (IterM.mk (Iterators.Types.DropWhile.mk (P := P) dropping it) m β : IterM m β)

/--
Constructs intermediate states of an iterator created with the combinator `IterM.dropWhileM`.
When `it.dropWhileM P` has stopped dropping elements, its new state cannot be created
directly with `IterM.dropWhileM` but only with `Intermediate.dropWhileM`.

`Intermediate.dropWhileM` is meant to be used only for internally or for verification purposes.
-/
@[always_inline, inline]
def IterM.Intermediate.dropWhileM [Monad m] (P : β → m (ULift Bool)) (dropping : Bool)
    (it : IterM (α := α) m β) :=
  (IterM.Intermediate.dropWhileWithPostcondition (PostconditionT.lift ∘ P) dropping it : IterM m β)

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
*Note: This is a very general combinator that requires an advanced understanding of monads,
dependent types and termination proofs. The variants `dropWhile` and `dropWhileM` are easier to use
and sufficient for most use cases.*

Given an iterator `it` and a monadic predicate `P`, `it.dropWhileWithPostcondition P` is an iterator
that emits the values emitted by `it` starting from the first value that is rejected by `P`.
The elements before are dropped.

`P` is expected to return `PostconditionT m (ULift Bool)`. The `PostconditionT` transformer allows
the caller to intrinsically prove properties about `P`'s return value in the monad `m`, enabling
termination proofs depending on the specific behavior of `P`.

**Marble diagram (ignoring monadic effects):**

Assuming that the predicate `P` accepts `a` and `b` but rejects `c`:

```text
it                                ---a----b---c--d-e--⊥
it.dropWhileWithPostcondition P   ------------c--d-e--⊥

it                                ---a----⊥
it.dropWhileWithPostcondition P   --------⊥
```

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is finite

Depending on `P`, it is possible that `it.dropWhileWithPostcondition P` is finite (or productive) although
`it` is not. In this case, the `Finite` (or `Productive`) instance needs to be proved manually.

**Performance:**

This combinator calls `P` on each output of `it` until the predicate evaluates to false. After
that, the combinator incurs an additional O(1) cost for each value emitted by `it`.
-/
@[always_inline, inline]
def IterM.dropWhileWithPostcondition (P : β → PostconditionT m (ULift Bool)) (it : IterM (α := α) m β) :=
  (Intermediate.dropWhileWithPostcondition P true it : IterM m β)

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
  (Intermediate.dropWhile P true it: IterM m β)

namespace Iterators.Types

/--
`it.PlausibleStep step` is the proposition that `step` is a possible next step from the
`dropWhile` iterator `it`. This is mostly internally relevant, except if one needs to manually
prove termination (`Finite` or `Productive` instances, for example) of a `dropWhile` iterator.
-/
inductive DropWhile.PlausibleStep [Iterator α m β] {P} (it : IterM (α := DropWhile α m β P) m β) :
    (step : IterStep (IterM (α := DropWhile α m β P) m β) β) → Prop where
  | yield : ∀ {it' out}, it.internalState.inner.IsPlausibleStep (.yield it' out) →
      it.internalState.dropping = false →
      PlausibleStep it (.yield (IterM.Intermediate.dropWhileWithPostcondition P false it') out)
  | skip : ∀ {it'}, it.internalState.inner.IsPlausibleStep (.skip it') →
      PlausibleStep it (.skip (IterM.Intermediate.dropWhileWithPostcondition P it.internalState.dropping it'))
  | done : it.internalState.inner.IsPlausibleStep .done → PlausibleStep it .done
  | start : ∀ {it' out}, it.internalState.inner.IsPlausibleStep (.yield it' out) →
      it.internalState.dropping = true → (P out).Property (.up false) →
      PlausibleStep it (.yield (IterM.Intermediate.dropWhileWithPostcondition P false it') out)
  | dropped : ∀ {it' out}, it.internalState.inner.IsPlausibleStep (.yield it' out) →
      it.internalState.dropping = true → (P out).Property (.up true) →
      PlausibleStep it (.skip (IterM.Intermediate.dropWhileWithPostcondition P true it'))

@[always_inline, inline]
instance DropWhile.instIterator [Monad m] [Iterator α m β] {P} :
    Iterator (DropWhile α m β P) m β where
  IsPlausibleStep := DropWhile.PlausibleStep
  step it := do
    match (← it.internalState.inner.step).inflate with
    | .yield it' out h =>
      if h' : it.internalState.dropping = true then
        match ← (P out).operation with
        | ⟨.up true, h''⟩ =>
          return .deflate <| .skip (IterM.Intermediate.dropWhileWithPostcondition P true it') (.dropped h h' h'')
        | ⟨.up false, h''⟩ =>
          return .deflate <| .yield (IterM.Intermediate.dropWhileWithPostcondition P false it') out (.start h h' h'')
      else
        return .deflate <| .yield (IterM.Intermediate.dropWhileWithPostcondition P false it') out
            (.yield h (Bool.not_eq_true _ ▸ h'))
    | .skip it' h =>
      return .deflate <| .skip (IterM.Intermediate.dropWhileWithPostcondition P it.internalState.dropping it') (.skip h)
    | .done h =>
      return .deflate <| .done (.done h)

private def DropWhile.instFinitenessRelation [Monad m] [Iterator α m β]
    [Finite α m] {P} :
    FinitenessRelation (DropWhile α m β P) m where
  rel := InvImage WellFoundedRelation.rel
      (IterM.finitelyManySteps ∘ DropWhile.inner ∘ IterM.internalState)
  wf := by
    apply InvImage.wf
    exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    cases h'
    case yield it' out k h' h'' =>
      cases h
      exact IterM.TerminationMeasures.Finite.rel_of_yield h'
    case skip it' out h' =>
      cases h
      exact IterM.TerminationMeasures.Finite.rel_of_skip h'
    case done _ =>
      cases h
    case start it' out h' h'' h''' =>
      cases h
      exact IterM.TerminationMeasures.Finite.rel_of_yield h'
    case dropped it' out h' h'' h''' =>
      cases h
      exact IterM.TerminationMeasures.Finite.rel_of_yield h'

instance DropWhile.instFinite [Monad m] [Iterator α m β] [Finite α m] {P} :
    Finite (DropWhile α m β P) m :=
  by exact Finite.of_finitenessRelation instFinitenessRelation

instance DropWhile.instIteratorLoopNew [Monad m] [Iterator α m β] :
    IteratorLoopNew (DropWhile α m β P) m n :=
  .defaultImplementation

instance DropWhile.instIteratorLoop [Monad m] [Monad n] [Iterator α m β] :
    IteratorLoop (DropWhile α m β P) m n :=
  .defaultImplementation

end Std.Iterators.Types
