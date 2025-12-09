/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers.Loop
public import Init.Data.Iterators.Internal.Termination
import Init.Control.Lawful.MonadAttach.Lemmas

@[expose] public section

/-!
This file provides the iterator combinator `IterM.drop`.
-/

namespace Std.Iterators

variable {α : Type w} {m : Type w → Type w'} {β : Type w}

/--
The internal state of the `IterM.drop` combinator.
-/
@[unbox]
structure Drop (α : Type w) (m : Type w → Type w') (β : Type w) where
  /-- Internal implementation detail of the iterator library -/
  remaining : Nat
  /-- Internal implementation detail of the iterator library -/
  inner : IterM (α := α) m β

/--
Given an iterator `it` and a natural number `n`, `it.drop n` is an iterator that forwards all of
`it`'s output values except for the first `n`.

**Marble diagram:**

```text
it          ---a----b---c--d-e--⊥
it.drop 3   ---------------d-e--⊥

it          ---a--⊥
it.drop 3   ------⊥
```

**Termination properties:**

* `Finite` instance: only if `it` is finite
* `Productive` instance: only if `it` is productive

**Performance:**

Currently, this combinator incurs an additional O(1) cost with each output of `it`, even when the iterator
does not drop any elements anymore.
-/
@[always_inline, inline]
def IterM.drop (n : Nat) (it : IterM (α := α) m β) :=
  toIterM (Drop.mk n it) m β

instance Drop.instIterator [Monad m] [Iterator α m β] : Iterator (Drop α m β) m β where
  step it := do
    match ← it.internalState.inner.step with
    | .yield it' out =>
      match it.internalState.remaining with
      | 0 => return .yield (it'.drop 0) out
      | k + 1 => return .skip (it'.drop k)
    | .skip it' =>
      return .skip (it'.drop it.internalState.remaining)
    | .done =>
      return .done

private def Drop.FiniteRel (m : Type w → Type w') [MonadAttach m] [Iterator α m β] [Finite α m] :
    IterM (α := Drop α m β) m β → IterM (α := Drop α m β) m β → Prop :=
  InvImage IterM.TerminationMeasures.Finite.Rel
    (IterM.finitelyManySteps ∘ Drop.inner ∘ IterM.internalState)

private def Drop.instFinitenessRelation
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Iterator α m β] [Finite α m] :
    FinitenessRelation (Drop α m β) m where
  rel := Drop.FiniteRel m
  wf := by
    apply InvImage.wf
    exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, hs, h⟩ := h
    obtain ⟨step', hs', h⟩ := LawfulMonadAttach.canReturn_bind_imp' h
    cases step', hs' using PlausibleIterStep.casesOn'
    · simp only at h
      split at h
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        cases hs
        exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        cases hs
        exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
    · cases LawfulMonadAttach.eq_of_canReturn_pure h
      cases hs
      exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›
    · cases LawfulMonadAttach.eq_of_canReturn_pure h
      nomatch hs

instance Drop.instFinite
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Iterator α m β] [Finite α m] :
    Finite (Drop α m β) m :=
  by exact Finite.of_finitenessRelation instFinitenessRelation

private def Drop.ProductiveRel (m : Type w → Type w')
    [Monad m] [MonadAttach m] [Iterator α m β] [Productive α m] :
    IterM (α := Drop α m β) m β → IterM (α := Drop α m β) m β → Prop :=
  InvImage (Prod.Lex Nat.lt_wfRel.rel IterM.TerminationMeasures.Productive.Rel)
    (fun it => (it.internalState.remaining, it.internalState.inner.finitelyManySkips))

private theorem Drop.productiveRel_of_remaining
    [Monad m] [MonadAttach m] [Iterator α m β] [Productive α m]
    {it it' : IterM (α := Drop α m β) m β}
    (h : it'.internalState.remaining < it.internalState.remaining) : Drop.ProductiveRel m it' it :=
  Prod.Lex.left _ _ h

private theorem Drop.productiveRel_of_inner
    [Monad m] [MonadAttach m] [Iterator α m β] [Productive α m] {remaining : Nat}
    {it it' : IterM (α := α) m β}
    (h : it'.finitelyManySkips.Rel it.finitelyManySkips) :
    Drop.ProductiveRel m (it'.drop remaining) (it.drop remaining) :=
  Prod.Lex.right _ h

private def Drop.instProductivenessRelation
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Iterator α m β] [Productive α m] :
    ProductivenessRelation (Drop α m β) m where
  rel := Drop.ProductiveRel m
  wf := by
    apply InvImage.wf
    exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, hs, h⟩ := LawfulMonadAttach.canReturn_bind_imp' h
    cases step, hs using PlausibleIterStep.casesOn'
    · simp only at h
      split at h
      · nomatch LawfulMonadAttach.eq_of_canReturn_pure h
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        apply productiveRel_of_remaining
        simp [IterM.drop, *]
    · cases LawfulMonadAttach.eq_of_canReturn_pure h
      apply productiveRel_of_inner
      apply IterM.TerminationMeasures.Productive.rel_of_skip
      assumption
    · nomatch LawfulMonadAttach.eq_of_canReturn_pure h

instance Drop.instProductive
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Iterator α m β] [Productive α m] :
    Productive (Drop α m β) m :=
  by exact Productive.of_productivenessRelation instProductivenessRelation

instance Drop.instIteratorCollect {n : Type w → Type w'} [Monad m] [MonadAttach m] [Monad n]
    [Iterator α m β] [Finite α m] : IteratorCollect (Drop α m β) m n :=
  .defaultImplementation

instance Drop.instIteratorLoop {n : Type x → Type x'} [Monad m] [MonadAttach m]
    [Monad n] [MonadAttach n] [Iterator α m β] : IteratorLoop (Drop α m β) m n :=
  .defaultImplementation

end Std.Iterators
