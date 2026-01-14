/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers.Loop

@[expose] public section

/-!
This file provides the iterator combinator `IterM.drop`.
-/

namespace Std

variable {α : Type w} {m : Type w → Type w'} {β : Type w}

/--
The internal state of the `IterM.drop` combinator.
-/
@[unbox]
structure Iterators.Types.Drop (α : Type w) (m : Type w → Type w') (β : Type w) where
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
  IterM.mk (Iterators.Types.Drop.mk n it) m β

namespace Iterators.Types

inductive Drop.PlausibleStep [Iterator α m β] (it : IterM (α := Drop α m β) m β) :
    (step : IterStep (IterM (α := Drop α m β) m β) β) → Prop where
  | drop : ∀ {it' out k}, it.internalState.inner.IsPlausibleStep (.yield it' out) →
      it.internalState.remaining = k + 1 → PlausibleStep it (.skip (it'.drop k))
  | skip : ∀ {it'}, it.internalState.inner.IsPlausibleStep (.skip it') →
      PlausibleStep it (.skip (it'.drop it.internalState.remaining))
  | done : it.internalState.inner.IsPlausibleStep .done → PlausibleStep it .done
  | yield : ∀ {it' out}, it.internalState.inner.IsPlausibleStep (.yield it' out) →
      it.internalState.remaining = 0 → PlausibleStep it (.yield (it'.drop 0) out)

instance Drop.instIterator [Monad m] [Iterator α m β] : Iterator (Drop α m β) m β where
  IsPlausibleStep := Drop.PlausibleStep
  step it := do
    match (← it.internalState.inner.step).inflate with
    | .yield it' out h =>
      match h' : it.internalState.remaining with
      | 0 => pure <| .deflate <| .yield (it'.drop 0) out (.yield h h')
      | k + 1 => pure <| .deflate <| .skip (it'.drop k) (.drop h h')
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.drop it.internalState.remaining) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (.done h)

private def Drop.FiniteRel (m : Type w → Type w') [Iterator α m β] [Finite α m] :
    IterM (α := Drop α m β) m β → IterM (α := Drop α m β) m β → Prop :=
  InvImage IterM.TerminationMeasures.Finite.Rel
    (IterM.finitelyManySteps ∘ Drop.inner ∘ IterM.internalState)

private def Drop.instFinitenessRelation [Iterator α m β] [Monad m]
    [Finite α m] :
    FinitenessRelation (Drop α m β) m where
  Rel := Drop.FiniteRel m
  wf := by
    apply InvImage.wf
    exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    cases h'
    case drop it' h' _ =>
      cases h
      apply IterM.TerminationMeasures.Finite.rel_of_yield
      exact h'
    case skip it' h' =>
      cases h
      apply IterM.TerminationMeasures.Finite.rel_of_skip
      exact h'
    case done h' =>
      cases h
    case yield it' out h' h'' =>
      cases h
      apply IterM.TerminationMeasures.Finite.rel_of_yield
      exact h'

instance Drop.instFinite [Iterator α m β] [Monad m] [Finite α m] :
    Finite (Drop α m β) m :=
  by exact Finite.of_finitenessRelation instFinitenessRelation

private def Drop.ProductiveRel (m : Type w → Type w') [Iterator α m β] [Productive α m] :
    IterM (α := Drop α m β) m β → IterM (α := Drop α m β) m β → Prop :=
  InvImage (Prod.Lex Nat.lt_wfRel.rel IterM.TerminationMeasures.Productive.Rel)
    (fun it => (it.internalState.remaining, it.internalState.inner.finitelyManySkips))

private theorem Drop.productiveRel_of_remaining [Monad m] [Iterator α m β] [Productive α m]
    {it it' : IterM (α := Drop α m β) m β}
    (h : it'.internalState.remaining < it.internalState.remaining) : Drop.ProductiveRel m it' it :=
  Prod.Lex.left _ _ h

private theorem Drop.productiveRel_of_inner [Monad m] [Iterator α m β] [Productive α m] {remaining : Nat}
    {it it' : IterM (α := α) m β}
    (h : it'.finitelyManySkips.Rel it.finitelyManySkips) :
    Drop.ProductiveRel m (it'.drop remaining) (it.drop remaining) :=
  Prod.Lex.right _ h

private def Drop.instProductivenessRelation [Iterator α m β] [Monad m]
    [Productive α m] :
    ProductivenessRelation (Drop α m β) m where
  Rel := Drop.ProductiveRel m
  wf := by
    apply InvImage.wf
    exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    rw [IterM.IsPlausibleSkipSuccessorOf] at h
    cases h
    case drop it' out k h h' =>
      apply productiveRel_of_remaining
      simp [h', IterM.drop]
    case skip it' h =>
      apply productiveRel_of_inner
      apply IterM.TerminationMeasures.Productive.rel_of_skip
      exact h

instance Drop.instProductive [Iterator α m β] [Monad m] [Productive α m] :
    Productive (Drop α m β) m :=
  by exact Productive.of_productivenessRelation instProductivenessRelation

instance Drop.instIteratorLoop {n : Type x → Type x'} [Monad m] [Monad n] [Iterator α m β] :
    IteratorLoop (Drop α m β) m n :=
  .defaultImplementation

end Std.Iterators.Types
