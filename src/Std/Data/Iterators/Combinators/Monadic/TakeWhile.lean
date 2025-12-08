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
public import Init.Control.Lawful.MonadAttach.Lemmas

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
-/

namespace Std.Iterators

variable {α : Type w} {m : Type w → Type w'} {β : Type w}

/--
Internal state of the `takeWhile` combinator. Do not depend on its internals.
-/
@[unbox]
structure TakeWhile (α : Type w) (m : Type w → Type w') (β : Type w)
    (P : β → m (ULift Bool)) where
  /-- Internal implementation detail of the iterator library. -/
  inner : IterM (α := α) m β

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
def IterM.takeWhileM [Monad m] (P : β → m (ULift Bool)) (it : IterM (α := α) m β) :
    IterM (α := TakeWhile α m β P) m β :=
  toIterM ⟨it⟩ m β

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
  (it.takeWhileM (pure ∘ ULift.up ∘ P) : IterM m β)

-- /--
-- `it.PlausibleStep step` is the proposition that `step` is a possible next step from the
-- `takeWhile` iterator `it`. This is mostly internally relevant, except if one needs to manually
-- prove termination (`Finite` or `Productive` instances, for example) of a `takeWhile` iterator.
-- -/
-- inductive TakeWhile.PlausibleStep [MonadAttach m] [Iterator α m β] {P}
--     (it : IterM (α := TakeWhile α m β P) m β) :
--     (step : IterStep (IterM (α := TakeWhile α m β P) m β) β) → Prop where
--   | yield : ∀ {it' out}, it.internalState.inner.IsPlausibleStep (.yield it' out) →
--       (P out).Property (.up true) → PlausibleStep it (.yield (it'.takeWhileWithPostcondition P) out)
--   | skip : ∀ {it'}, it.internalState.inner.IsPlausibleStep (.skip it') →
--       PlausibleStep it (.skip (it'.takeWhileWithPostcondition P))
--   | done : it.internalState.inner.IsPlausibleStep .done → PlausibleStep it .done
--   | rejected : ∀ {it' out}, it.internalState.inner.IsPlausibleStep (.yield it' out) →
--       (P out).Property (.up false) → PlausibleStep it .done

@[always_inline, inline]
instance TakeWhile.instIterator [Monad m] [Iterator α m β] {P} :
    Iterator (TakeWhile α m β P) m β where
  step it := do
    match ← it.internalState.inner.step with
    | .yield it' out => return match ← P out with
      | .up true => .yield (it'.takeWhileM P) out
      | .up false => .done
    | .skip it' => return .skip (it'.takeWhileM P)
    | .done => return .done

private def TakeWhile.instFinitenessRelation
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Iterator α m β] [Finite α m] {P} : FinitenessRelation (TakeWhile α m β P) m where
  rel := InvImage WellFoundedRelation.rel (IterM.finitelyManySteps ∘ TakeWhile.inner ∘ IterM.internalState)
  wf := by
    apply InvImage.wf
    exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, hs, h⟩ := h
    obtain ⟨step', hs', h'⟩ := LawfulMonadAttach.canReturn_bind_imp' h
    cases step', hs' using PlausibleIterStep.casesOn'
    · obtain ⟨Px, hPx, h'⟩ := LawfulMonadAttach.canReturn_bind_imp' h'
      cases LawfulMonadAttach.eq_of_canReturn_pure h'
      split at hs
      · cases hs
        exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
      · cases hs
    · cases LawfulMonadAttach.eq_of_canReturn_pure h'
      cases hs
      exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›
    · cases LawfulMonadAttach.eq_of_canReturn_pure h'
      cases hs

instance TakeWhile.instFinite
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Iterator α m β] [Finite α m] {P} :
    Finite (TakeWhile α m β P) m :=
  by exact Finite.of_finitenessRelation instFinitenessRelation

private def TakeWhile.instProductivenessRelation
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Iterator α m β] [Productive α m] {P} :
    ProductivenessRelation (TakeWhile α m β P) m where
  rel := InvImage WellFoundedRelation.rel (IterM.finitelyManySkips ∘ TakeWhile.inner ∘ IterM.internalState)
  wf := by
    apply InvImage.wf
    exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, hs, h⟩ := LawfulMonadAttach.canReturn_bind_imp' h
    cases step, hs using PlausibleIterStep.casesOn'
    · obtain ⟨Px, hPx, h⟩ := LawfulMonadAttach.canReturn_bind_imp' h
      have := LawfulMonadAttach.eq_of_canReturn_pure h
      split at this <;> cases this
    · cases LawfulMonadAttach.eq_of_canReturn_pure h
      exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›
    · cases LawfulMonadAttach.eq_of_canReturn_pure h

instance TakeWhile.instProductive
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Iterator α m β] [Productive α m] {P} :
    Productive (TakeWhile α m β P) m :=
  by exact Productive.of_productivenessRelation instProductivenessRelation

instance TakeWhile.instIteratorCollect
    [Monad m] [MonadAttach m] [Monad n]
    [Iterator α m β] [Productive α m] {P} :
    IteratorCollect (TakeWhile α m β P) m n :=
  .defaultImplementation

instance TakeWhile.instIteratorLoop
    [Monad m] [MonadAttach m] [Monad n] [MonadAttach n]
    [Iterator α m β] [IteratorLoop α m n] :
    IteratorLoop (TakeWhile α m β P) m n :=
  .defaultImplementation

end Std.Iterators
