/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Internal.Termination
public import Init.Data.Iterators.Consumers.Monadic.Access
import all Init.Data.Iterators.Consumers.Monadic.Access
public import Init.Data.Iterators.Consumers.Monadic.Collect
public import Init.Data.Iterators.Consumers.Monadic.Loop
import Init.Control.Lawful.MonadAttach.Lemmas

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

instance
    [Monad m] [Iterator α m β] [IteratorAccess α m] :
    Iterator (Types.StepSizeIterator α m β) m β where
  step it := (fun s => s.mapIterator (⟨⟨it.internalState.n, it.internalState.n, ·⟩⟩)) <$>
    it.internalState.inner.nextAtIdx? it.internalState.nextIdx

def Types.StepSizeIterator.instFinitenessRelation
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Iterator α m β] [IteratorAccess α m] [LawfulIteratorAccess α m]
    [Finite α m] : FinitenessRelation (Types.StepSizeIterator α m β) m where
  rel := InvImage WellFoundedRelation.rel (fun it => it.internalState.inner.finitelyManySteps)
  wf := by
    apply InvImage.wf
    apply WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, hs, h⟩ := h
    obtain ⟨step', hs', rfl⟩ := LawfulMonadAttach.canReturn_map_imp' h
    replace hs' := LawfulIteratorAccess.isPlausibleNthOutputStep_of_canReturn hs'
    clear h
    obtain ⟨⟨n, it⟩⟩ := it
    simp only at ⊢ hs'
    induction hs'
    case zero_yield =>
      cases hs
      exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
    case done =>
      simp_all [IterStep.successor]
    case yield ih =>
      apply Relation.TransGen.trans
      · exact ih hs
      · exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
    case skip ih  =>
      apply Relation.TransGen.trans
      · exact ih hs
      · exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›

instance Types.StepSizeIterator.instFinite
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Iterator α m β] [IteratorAccess α m] [LawfulIteratorAccess α m] [Finite α m] :
    Finite (Types.StepSizeIterator α m β) m :=
  .of_finitenessRelation instFinitenessRelation

def Types.StepSizeIterator.instProductivenessRelation
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Iterator α m β] [IteratorAccess α m] [LawfulIteratorAccess α m] [Productive α m] :
    ProductivenessRelation (Types.StepSizeIterator α m β) m where
  rel := InvImage WellFoundedRelation.rel (fun it => it.internalState.inner.finitelyManySkips)
  wf := by
    apply InvImage.wf
    apply WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step', hs', h'⟩ := LawfulMonadAttach.canReturn_map_imp' h
    replace hs' := LawfulIteratorAccess.isPlausibleNthOutputStep_of_canReturn hs'
    cases step'
    · cases h'
    · exfalso
      exact IterM.not_isPlausibleNthOutputStep_skip hs'
    · cases h'

instance Types.StepSizeIterator.instProductive
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Iterator α m β] [IteratorAccess α m] [LawfulIteratorAccess α m] [Productive α m] :
    Productive (Types.StepSizeIterator α m β) m :=
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
    [IteratorAccess α m] [Monad m] [MonadAttach m] [Monad n] :
    IteratorCollect (Types.StepSizeIterator α m β) m n :=
  .defaultImplementation

instance Types.StepSizeIterator.instIteratorLoop {m n} [Iterator α m β]
    [IteratorAccess α m] [Monad m] [MonadAttach m] [MonadAttach n] [Monad n] :
    IteratorLoop (Types.StepSizeIterator α m β) m n :=
  .defaultImplementation

end Std.Iterators
