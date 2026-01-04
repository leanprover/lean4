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
public import Init.Data.Iterators.PostconditionMonad

@[expose] public section

/-!
# Monadic `takeWhile` iterator combinator

This module provides the iterator combinator `IterM.takeWhile` that will take all values emitted
by a given iterator until a given predicate on these values becomes false the first time. Then
the combinator will terminate.

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
Internal state of the `takeWhile` combinator. Do not depend on its internals.
-/
@[unbox]
structure Iterators.Types.TakeWhile (α : Type w) (m : Type w → Type w') (β : Type w)
    (P : β → PostconditionT m (ULift Bool)) where
  /-- Internal implementation detail of the iterator library. -/
  inner : IterM (α := α) m β

/--
*Note: This is a very general combinator that requires an advanced understanding of monads,
dependent types and termination proofs. The variants `takeWhile` and `takeWhileM` are easier to use
and sufficient for most use cases.*

Given an iterator `it` and a monadic predicate `P`, `it.takeWhileWithPostcondition P` is an iterator
that emits the values emitted by `it` until one of those values is rejected by `P`.
If some emitted value is rejected by `P`, the value is dropped and the iterator terminates.

`P` is expected to return `PostconditionT m (ULift Bool)`. The `PostconditionT` transformer allows
the caller to intrinsically prove properties about `P`'s return value in the monad `m`, enabling
termination proofs depending on the specific behavior of `P`.

**Marble diagram (ignoring monadic effects):**

Assuming that the predicate `P` accepts `a` and `b` but rejects `c`:

```text
it                                ---a----b---c--d-e--⊥
it.takeWhileWithPostcondition P   ---a----b---⊥

it                                ---a----⊥
it.takeWhileWithPostcondition P   ---a----⊥
```

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

Depending on `P`, it is possible that `it.takeWhileWithPostcondition P` is finite (or productive)
although `it` is not. In this case, the `Finite` (or `Productive`) instance needs to be proved
manually.

**Performance:**

This combinator calls `P` on each output of `it` until the predicate evaluates to false. Then
it terminates.
-/
@[always_inline, inline]
def IterM.takeWhileWithPostcondition (P : β → PostconditionT m (ULift Bool)) (it : IterM (α := α) m β) :=
  (IterM.mk (Types.TakeWhile.mk (P := P) it) m β : IterM m β)

/--
Given an iterator `it` and a monadic predicate `P`, `it.takeWhileM P` is an iterator that outputs
the values emitted by `it` until one of those values is rejected by `P`.
If some emitted value is rejected by `P`, the value is dropped and the iterator terminates.

If `P` is pure, then the simpler variant `takeWhile` can be used instead.

**Marble diagram (ignoring monadic effects):**

Assuming that the predicate `P` accepts `a` and `b` but rejects `c`:

```text
it                ---a----b---c--d-e--⊥
it.takeWhileM P   ---a----b---⊥

it                ---a----⊥
it.takeWhileM P   ---a----⊥
```

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

Depending on `P`, it is possible that `it.takeWhileM P` is finite (or productive) although `it` is not.
In this case, the `Finite` (or `Productive`) instance needs to be proved manually.

**Performance:**

This combinator calls `P` on each output of `it` until the predicate evaluates to false. Then
it terminates.
-/
@[always_inline, inline]
def IterM.takeWhileM [Monad m] [MonadAttach m] (P : β → m (ULift Bool)) (it : IterM (α := α) m β) :=
  (it.takeWhileWithPostcondition (PostconditionT.attachLift ∘ P) : IterM m β)

/--
Given an iterator `it` and a predicate `P`, `it.takeWhile P` is an iterator that outputs
the values emitted by `it` until one of those values is rejected by `P`.
If some emitted value is rejected by `P`, the value is dropped and the iterator terminates.

In situations where `P` is monadic, use `takeWhileM` instead.

**Marble diagram (ignoring monadic effects):**

Assuming that the predicate `P` accepts `a` and `b` but rejects `c`:

```text
it               ---a----b---c--d-e--⊥
it.takeWhile P   ---a----b---⊥

it               ---a----⊥
it.takeWhile P   ---a----⊥
```

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

Depending on `P`, it is possible that `it.takeWhile P` is finite (or productive) although `it` is not.
In this case, the `Finite` (or `Productive`) instance needs to be proved manually.

**Performance:**

This combinator calls `P` on each output of `it` until the predicate evaluates to false. Then
it terminates.
-/
@[always_inline, inline]
def IterM.takeWhile [Monad m] (P : β → Bool) (it : IterM (α := α) m β) :=
  (it.takeWhileWithPostcondition (pure ∘ ULift.up ∘ P) : IterM m β)

namespace Iterators.Types

/--
`it.PlausibleStep step` is the proposition that `step` is a possible next step from the
`takeWhile` iterator `it`. This is mostly internally relevant, except if one needs to manually
prove termination (`Finite` or `Productive` instances, for example) of a `takeWhile` iterator.
-/
inductive TakeWhile.PlausibleStep [Iterator α m β] {P} (it : IterM (α := TakeWhile α m β P) m β) :
    (step : IterStep (IterM (α := TakeWhile α m β P) m β) β) → Prop where
  | yield : ∀ {it' out}, it.internalState.inner.IsPlausibleStep (.yield it' out) →
      (P out).Property (.up true) → PlausibleStep it (.yield (it'.takeWhileWithPostcondition P) out)
  | skip : ∀ {it'}, it.internalState.inner.IsPlausibleStep (.skip it') →
      PlausibleStep it (.skip (it'.takeWhileWithPostcondition P))
  | done : it.internalState.inner.IsPlausibleStep .done → PlausibleStep it .done
  | rejected : ∀ {it' out}, it.internalState.inner.IsPlausibleStep (.yield it' out) →
      (P out).Property (.up false) → PlausibleStep it .done

@[always_inline, inline]
instance TakeWhile.instIterator [Monad m] [Iterator α m β] {P} :
    Iterator (TakeWhile α m β P) m β where
  IsPlausibleStep := TakeWhile.PlausibleStep
  step it := do
    match (← it.internalState.inner.step).inflate with
    | .yield it' out h => match ← (P out).operation with
      | ⟨.up true, h'⟩ => pure <| .deflate <| .yield (it'.takeWhileWithPostcondition P) out (.yield h h')
      | ⟨.up false, h'⟩ => pure <| .deflate <| .done (.rejected h h')
    | .skip it' h => pure <| .deflate <| .skip (it'.takeWhileWithPostcondition P) (.skip h)
    | .done h => pure <| .deflate <| .done (.done h)

private def TakeWhile.instFinitenessRelation [Monad m] [Iterator α m β]
    [Finite α m] {P} :
    FinitenessRelation (TakeWhile α m β P) m where
  Rel := InvImage WellFoundedRelation.rel (IterM.finitelyManySteps ∘ TakeWhile.inner ∘ IterM.internalState)
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
    case rejected _ =>
      cases h

instance TakeWhile.instFinite [Monad m] [Iterator α m β] [Finite α m] {P} :
    Finite (TakeWhile α m β P) m :=
  by exact Finite.of_finitenessRelation instFinitenessRelation

private def TakeWhile.instProductivenessRelation [Monad m] [Iterator α m β]
    [Productive α m] {P} :
    ProductivenessRelation (TakeWhile α m β P) m where
  Rel := InvImage WellFoundedRelation.rel (IterM.finitelyManySkips ∘ TakeWhile.inner ∘ IterM.internalState)
  wf := by
    apply InvImage.wf
    exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    cases h
    exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›

instance TakeWhile.instProductive [Monad m] [Iterator α m β] [Productive α m] {P} :
    Productive (TakeWhile α m β P) m :=
  by exact Productive.of_productivenessRelation instProductivenessRelation

instance TakeWhile.instIteratorLoop [Monad m] [Monad n] [Iterator α m β]
    [IteratorLoop α m n] :
    IteratorLoop (TakeWhile α m β P) m n :=
  .defaultImplementation

end Std.Iterators.Types
