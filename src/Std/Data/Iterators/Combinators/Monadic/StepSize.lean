/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Internal.Termination
public import Init.Data.Iterators.Consumers.Monadic.Access
public import Init.Data.Iterators.Consumers.Monadic.Collect
public import Init.Data.Iterators.Consumers.Monadic.Loop

@[expose] public section

/-!
This module implements a combinator that only yields every `n`-th element of another iterator.
-/

namespace Std.Iterators

@[unbox]
structure Types.StepSizeIterator (α : Type w) (m : Type w → Type w') (β : Type w) where
  nextIdx : Nat
  n : Nat
  inner : IterM (α := α) m β

instance [Iterator α m β] [IteratorAccess α m] [Monad m] :
    Iterator (Types.StepSizeIterator α m β) m β where
  IsPlausibleStep it step :=
    it.internalState.inner.IsPlausibleNthOutputStep it.internalState.nextIdx
        (step.mapIterator (Types.StepSizeIterator.inner ∘ IterM.internalState)) ∧
      ∀ it' out, step = .yield it' out →
        it'.internalState.n = it.internalState.n ∧ it'.internalState.nextIdx = it.internalState.n
  step it := (fun s => .deflate ⟨s.1.mapIterator (⟨⟨it.internalState.n, it.internalState.n, ·⟩⟩), by
      simp only [IterStep.mapIterator_mapIterator]
      refine cast ?_ s.property
      rw (occs := [1]) [← IterStep.mapIterator_id (step := s.val)]
      congr, by
      intro it' out
      cases s.val
      · simp only [IterStep.mapIterator_yield, IterStep.yield.injEq, and_imp]
        rintro h _
        simp [← h]
      · simp
      · simp
      done⟩) <$> it.internalState.inner.nextAtIdx? it.internalState.nextIdx

def Types.StepSizeIterator.instFinitenessRelation [Iterator α m β] [IteratorAccess α m] [Monad m]
    [Finite α m] : FinitenessRelation (Types.StepSizeIterator α m β) m where
  rel := InvImage WellFoundedRelation.rel (fun it => it.internalState.inner.finitelyManySteps)
  wf := by
    apply InvImage.wf
    apply WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, hs, h⟩ := h
    simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep] at h
    simp only [InvImage]
    obtain ⟨⟨n, it⟩⟩ := it
    simp only at ⊢ h
    generalize h' : step.mapIterator (Types.StepSizeIterator.inner ∘ IterM.internalState) = s at h
    replace h := h.1
    induction h
    case zero_yield =>
      cases step <;> (try exfalso; simp at h'; done)
      cases hs; cases h'
      apply IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
    case done =>
      cases step <;> simp_all [IterStep.successor]
    case yield ih =>
      apply Relation.TransGen.trans
      · exact ih h'
      · exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
    case skip ih  =>
      apply Relation.TransGen.trans
      · exact ih h'
      · exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›

instance Types.StepSizeIterator.instFinite [Iterator α m β] [IteratorAccess α m] [Monad m]
    [Finite α m] : Finite (Types.StepSizeIterator α m β) m :=
  .of_finitenessRelation instFinitenessRelation

def Types.StepSizeIterator.instProductivenessRelation [Iterator α m β] [IteratorAccess α m] [Monad m]
    [Productive α m] : ProductivenessRelation (Types.StepSizeIterator α m β) m where
  rel := InvImage WellFoundedRelation.rel (fun it => it.internalState.inner.finitelyManySkips)
  wf := by
    apply InvImage.wf
    apply WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp only [IterM.IsPlausibleSkipSuccessorOf, IterM.IsPlausibleStep, Iterator.IsPlausibleStep] at h
    simp only [InvImage]
    obtain ⟨⟨n, it⟩⟩ := it
    simp only [IterStep.mapIterator_skip, Function.comp_apply] at ⊢ h
    generalize h' : IterStep.skip _ = s at h
    exfalso
    replace h := h.1
    induction h
    case zero_yield => cases h'
    case done => cases h'
    case yield hp ih => exact ih h'
    case skip ih  => exact ih h'

instance Types.StepSizeIterator.instProductive [Iterator α m β] [IteratorAccess α m] [Monad m]
    [Productive α m] : Productive (Types.StepSizeIterator α m β) m :=
  .of_productivenessRelation instProductivenessRelation

/--
Produces an iterator that emits one value of `it`, then drops `n - 1` elements, then emits another
value, and so on. In other words, it emits every `n`-th value of `it`, starting with the first one.

If `n = 0`, the iterator behaves like for `n = 1`: It emits all values of `it`.


**Marble diagram:**

```
it               ---1----2----3---4----5
it.stepSize 2    ---1---------3--------5
```

**Availability:**

This operation is currently only available for iterators implementing `IteratorAccess`,
such as `PRange.iter` range iterators.

**Termination properties:**

* `Finite` instance: only if the base iterator `it` is finite
* `Productive` instance: always
-/
@[always_inline, inline]
def IterM.stepSize [Iterator α m β] [IteratorAccess α m] [Monad m]
    (it : IterM (α := α) m β) (n : Nat) :
    IterM (α := Types.StepSizeIterator α m β) m β :=
  ⟨⟨0, n - 1, it⟩⟩

instance Types.StepSizeIterator.instIteratorCollect {m n} [Iterator α m β]
    [IteratorAccess α m] [Monad m] [Monad n] :
    IteratorCollect (Types.StepSizeIterator α m β) m n :=
  .defaultImplementation

instance Types.StepSizeIterator.instIteratorCollectPartial {m n} [Iterator α m β]
    [IteratorAccess α m] [Monad m] [Monad n] :
    IteratorCollectPartial (Types.StepSizeIterator α m β) m n :=
  .defaultImplementation

instance Types.StepSizeIterator.instIteratorLoop {m n} [Iterator α m β]
    [IteratorAccess α m] [Monad m] [Monad n] :
    IteratorLoop (Types.StepSizeIterator α m β) m n :=
  .defaultImplementation

instance Types.StepSizeIterator.instIteratorLoopPartial {m n} [Iterator α m β]
    [IteratorAccess α m] [Monad m] [Monad n] :
    IteratorLoopPartial (Types.StepSizeIterator α m β) m n :=
  .defaultImplementation

instance Types.StepSizeIterator.instIteratorSize [Iterator α Id β]
    [IteratorAccess α Id] [Finite (Types.StepSizeIterator α Id β) Id] :
    IteratorSize (Types.StepSizeIterator α Id β) Id :=
  .defaultImplementation

instance Types.StepSizeIterator.instIteratorSizePartial [Iterator α Id β]
    [IteratorAccess α Id] :
    IteratorSizePartial (Types.StepSizeIterator α Id β) Id :=
  .defaultImplementation

end Std.Iterators
