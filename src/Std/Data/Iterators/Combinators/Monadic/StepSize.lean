/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Data.Iterators.Basic
import Init.Data.Iterators.Internal.Termination
import Init.Data.Iterators.Consumers.Monadic.Access
import Init.Data.Iterators.Consumers.Monadic.Collect
import Init.Data.Iterators.Consumers.Monadic.Loop

namespace Std.Iterators

@[unbox]
structure Types.StepSizeIterator (α : Type w) (m : Type w → Type w') (β : Type w) where
  n : Nat
  inner : IterM (α := α) m β

instance [Iterator α m β] [IteratorAccess α m] [Monad m] :
    Iterator (Types.StepSizeIterator α m β) m β where
  IsPlausibleStep it step :=
    it.internalState.inner.IsPlausibleNthOutput it.internalState.n
      (step.mapIterator (Types.StepSizeIterator.inner ∘ IterM.internalState))
  step it := (fun s => ⟨s.1.mapIterator (⟨⟨it.internalState.n, ·⟩⟩), by
      simp only [IterStep.mapIterator_mapIterator]
      refine cast ?_ s.property
      rw (occs := [1]) [← IterStep.mapIterator_id (step := s.val)]
      congr⟩) <$> it.internalState.inner.nextAtIdx? it.internalState.n

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
    induction h
    case zero_yield => cases h'
    case done => cases h'
    case yield hp ih => exact ih h'
    case skip ih  => exact ih h'

instance Types.StepSizeIterator.instProductive [Iterator α m β] [IteratorAccess α m] [Monad m]
    [Productive α m] : Productive (Types.StepSizeIterator α m β) m :=
  .of_productivenessRelation instProductivenessRelation

/--
Produces an iterator that drops `n - 1` values of `it` and then emits one value, then drops `n - 1`
values again, and so on. In other words, it emits every `n`-th value of `it`.

If `n = 0`, the iterator behaves like for `n = 1`: It emits all values of `it`.

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
  ⟨⟨n - 1, it⟩⟩

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

instance Types.StepSizeIterator.instIteratorSize {m} [Iterator α m β]
    [IteratorAccess α m] [Monad m] [Finite (Types.StepSizeIterator α m β) m] :
    IteratorSize (Types.StepSizeIterator α m β) m :=
  .defaultImplementation

instance Types.StepSizeIterator.instIteratorSizePartial {m} [Iterator α m β]
    [IteratorAccess α m] [Monad m] :
    IteratorSizePartial (Types.StepSizeIterator α m β) m :=
  .defaultImplementation

end Std.Iterators
