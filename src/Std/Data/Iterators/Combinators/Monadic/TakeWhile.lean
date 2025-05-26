/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Data.Nat.Lemmas
import Init.RCases
import Std.Data.Iterators.Basic
import Std.Data.Iterators.Consumers.Monadic.Collect
import Std.Data.Iterators.Consumers.Monadic.Loop
import Std.Data.Iterators.Internal.Termination
import Std.Data.Iterators.PostConditionMonad

/-!
This module provides the iterator combinator `IterM.takeWhile`.
-/

namespace Std.Iterators

variable {α : Type w} {m : Type w → Type w'} {n : Type w → Type w''} {β : Type w}

@[unbox]
structure TakeWhile (α : Type w) (m : Type w → Type w') (β : Type w)
    (P : β → PostconditionT m (ULift Bool)) where
  inner : IterM (α := α) m β

/--
*Note: This is a very general combinator that requires an advanced understanding of monads,
dependent types and termination proofs. The variants `takeWhile` and `takeWhileM` are easier to use
and sufficient for most use cases.*

Given an iterator `it` and a monadic predicate `P`, `it.takeWhileWithProof P` is an iterator that
emits the values emitted by `it` until one of those values is rejected by `P`.
If some emitted value is rejected by `P`, the value is dropped and the iterator terminates.

`P` is expected to return `PostconditionT m (ULift Bool)`. The `PostconditionT` transformer allows
the caller to intrinsically prove properties about `f`'s return value in the monad `m`, enabling
termination proofs depending on the specific behavior of `f`.

**Marble diagram (ignoring monadic effects):**

Assuming that the predicate `P` accepts `a` and `b` but rejects `c`:

```text
it                        ---a----b---c--d-e--⊥
it.takeWhileWithProof P   ---a----b---⊥

it                        ---a----⊥
it.takeWhileWithProof P   ---a----⊥
```

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

Depending on `P`, it is possible that `it.takeWhileWithProof P` is finite (or productive) although `it` is not.
In this case, the `Finite` (or `Productive`) instance needs to be proved manually.

**Performance:**

This combinator calls `P` on each output of `it` until the predicate evaluates to false. Then
it terminates.
-/
@[always_inline, inline]
def IterM.takeWhileWithProof (P : β → PostconditionT m (ULift Bool)) (it : IterM (α := α) m β) :=
  (toIterM (TakeWhile.mk (P := P) it) m β : IterM m β)

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
def IterM.takeWhileM [Monad m] (P : β → m (ULift Bool)) (it : IterM (α := α) m β) :=
  (it.takeWhileWithProof (monadLift ∘ P) : IterM m β)

/--
Given an iterator `it` and a predicate `P`, `it.takeWhile P` is an iterator that outputs
the values emitted by `it` until one of those values is rejected by `P`.
If some emitted value is rejected by `P`, the value is dropped and the iterator terminates.

In situations where `f` is monadic, use `takeWhileM` instead.

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

inductive TakeWhile.PlausibleStep [Iterator α m β] {P} (it : IterM (α := TakeWhile α m β P) m β) :
    (step : IterStep (IterM (α := TakeWhile α m β P) m β) β) → Prop where
  | yield : ∀ {it' out}, it.internalState.inner.IsPlausibleStep (.yield it' out) →
      (P out).Property (.up true) → PlausibleStep it (.yield (it'.takeWhileWithProof P) out)
  | skip : ∀ {it'}, it.internalState.inner.IsPlausibleStep (.skip it') →
      PlausibleStep it (.skip (it'.takeWhileWithProof P))
  | done : it.internalState.inner.IsPlausibleStep .done → PlausibleStep it .done
  | rejected : ∀ {it' out}, it.internalState.inner.IsPlausibleStep (.yield it' out) →
      (P out).Property (.up false) → PlausibleStep it .done

@[always_inline, inline]
instance TakeWhile.instIterator [Monad m] [Iterator α m β] {P} :
    Iterator (TakeWhile α m β P) m β where
  IsPlausibleStep := TakeWhile.PlausibleStep
  step it := do
    match ← it.internalState.inner.step with
    | .yield it' out h => match ← (P out).operation with
      | ⟨.up true, h'⟩ => pure <| .yield (it'.takeWhileWithProof P) out (.yield h h')
      | ⟨.up false, h'⟩ => pure <| .done (.rejected h h')
    | .skip it' h => pure <| .skip (it'.takeWhileWithProof P) (.skip h)
    | .done h => pure <| .done (.done h)

private def TakeWhile.instFinitenessRelation [Monad m] [Iterator α m β]
    [Finite α m] {P} :
    FinitenessRelation (TakeWhile α m β P) m where
  rel := InvImage WellFoundedRelation.rel (IterM.finitelyManySteps ∘ TakeWhile.inner ∘ IterM.internalState)
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
  Finite.of_finitenessRelation instFinitenessRelation

private def TakeWhile.instProductivenessRelation [Monad m] [Iterator α m β]
    [Finite α m] {P} :
    ProductivenessRelation (TakeWhile α m β P) m where
  rel := InvImage WellFoundedRelation.rel (IterM.finitelyManySkips ∘ TakeWhile.inner ∘ IterM.internalState)
  wf := by
    apply InvImage.wf
    exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    cases h
    exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›

instance TakeWhile.instProductive [Monad m] [Iterator α m β] [Finite α m] {P} :
    Productive (TakeWhile α m β P) m :=
  Productive.of_productivenessRelation instProductivenessRelation

instance TakeWhile.instIteratorCollect [Monad m] [Monad n] [Iterator α m β] [Productive α m] {P} :
    IteratorCollect (TakeWhile α m β P) m n :=
  .defaultImplementation

instance TakeWhile.instIteratorCollectPartial [Monad m] [Monad n] [Iterator α m β] {P} :
    IteratorCollectPartial (TakeWhile α m β P) m n :=
  .defaultImplementation

private def TakeWhile.PlausibleForInStep {β : Type u} {γ : Type v}
    (P : β → PostconditionT m (ULift Bool))
    (f : β → γ → ForInStep γ → Prop) :
    β → γ → (ForInStep γ) → Prop
  | out, c, ForInStep.yield c' => (P out).Property (.up true) ∧ f out c (.yield c')
  | _, _, .done _ => True

private def TakeWhile.wellFounded_plausibleForInStep {α β : Type w} {m : Type w → Type w'}
    [Monad m] [Iterator α m β] {γ : Type x} {P}
    {f : β → γ → ForInStep γ → Prop} (wf : IteratorLoop.WellFounded (TakeWhile α m β P) m f) :
    IteratorLoop.WellFounded α m (PlausibleForInStep P f) := by
      simp only [IteratorLoop.WellFounded] at ⊢ wf
      letI : WellFoundedRelation _ := ⟨_, wf⟩
      apply Subrelation.wf
        (r := InvImage WellFoundedRelation.rel fun p => (p.1.takeWhileWithProof P, p.2))
        (fun {p q} h => by
          simp only [InvImage, WellFoundedRelation.rel, this, IteratorLoop.rel,
            IterM.IsPlausibleStep, Iterator.IsPlausibleStep]
          obtain ⟨out, h, h'⟩ | ⟨h, h'⟩ := h
          · apply Or.inl
            exact ⟨out, .yield h h'.1, h'.2⟩
          · apply Or.inr
            refine ⟨?_, h'⟩
            exact PlausibleStep.skip h)
      apply InvImage.wf
      exact WellFoundedRelation.wf

instance TakeWhile.instIteratorFor [Monad m] [Monad n] [Iterator α m β]
    [IteratorLoop α m n] [MonadLiftT m n] :
    IteratorLoop (TakeWhile α m β P) m n where
  forIn lift {γ} Plausible wf it init f := by
    refine IteratorLoop.forIn lift (γ := γ)
        (PlausibleForInStep P Plausible)
        (wellFounded_plausibleForInStep wf)
        it.internalState.inner
        init
        fun out acc => do match ← (P out).operation with
          | ⟨.up true, h⟩ => match ← f out acc with
            | ⟨.yield c, h'⟩ => pure ⟨.yield c, h, h'⟩
            | ⟨.done c, h'⟩ => pure ⟨.done c, .intro⟩
          | ⟨.up false, h⟩ => pure ⟨.done acc, .intro⟩

instance TakeWhile.instIteratorForPartial [Monad m] [Monad n] [Iterator α m β]
    [IteratorLoopPartial α m n] [MonadLiftT m n] {P} :
    IteratorLoopPartial (TakeWhile α m β P) m n where
  forInPartial lift {γ} it init f := do
    IteratorLoopPartial.forInPartial lift it.internalState.inner (γ := γ)
        init
        fun out acc => do match ← (P out).operation with
          | ⟨.up true, _⟩ => match ← f out acc with
            | .yield c => pure (.yield c)
            | .done c => pure (.done c)
          | ⟨.up false, _⟩ => pure (.done acc)

end Std.Iterators
