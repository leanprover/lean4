/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Data.Nat.Lemmas
import Init.RCases
import Init.Data.Iterators.Basic
import Init.Data.Iterators.Consumers.Monadic.Collect
import Init.Data.Iterators.Consumers.Monadic.Loop
import Init.Data.Iterators.Internal.Termination

/-!
This module provides the iterator combinator `IterM.take`.
-/

namespace Std.Iterators

variable {α : Type w} {m : Type w → Type w'} {n : Type w → Type w''} {β : Type w}

/--
The internal state of the `IterM.take` iterator combinator.
-/
@[unbox]
structure Take (α : Type w) (m : Type w → Type w') (β : Type w) where
  /-- Internal implementation detail of the iterator library -/
  remaining : Nat
  /-- Internal implementation detail of the iterator library -/
  inner : IterM (α := α) m β

/--
Given an iterator `it` and a natural number `n`, `it.take n` is an iterator that outputs
up to the first `n` of `it`'s values in order and then terminates.

**Marble diagram:**

```text
it          ---a----b---c--d-e--⊥
it.take 3   ---a----b---c⊥

it          ---a--⊥
it.take 3   ---a--⊥
```

**Termination properties:**

* `Finite` instance: only if `it` is productive
* `Productive` instance: only if `it` is productive

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it`.
-/
@[always_inline, inline]
def IterM.take (n : Nat) (it : IterM (α := α) m β) :=
  toIterM (Take.mk n it) m β

theorem IterM.take.surjective {α : Type w} {m : Type w → Type w'} {β : Type w}
    (it : IterM (α := Take α m β) m β) :
    ∃ (it₀ : IterM (α := α) m β) (k : Nat), it = it₀.take k := by
  refine ⟨it.internalState.inner, it.internalState.remaining, rfl⟩

inductive Take.PlausibleStep [Iterator α m β] (it : IterM (α := Take α m β) m β) :
    (step : IterStep (IterM (α := Take α m β) m β) β) → Prop where
  | yield : ∀ {it' out k}, it.internalState.inner.IsPlausibleStep (.yield it' out) →
      it.internalState.remaining = k + 1 → PlausibleStep it (.yield (it'.take k) out)
  | skip : ∀ {it' k}, it.internalState.inner.IsPlausibleStep (.skip it') →
      it.internalState.remaining = k + 1 → PlausibleStep it (.skip (it'.take (k + 1)))
  | done : it.internalState.inner.IsPlausibleStep .done → PlausibleStep it .done
  | depleted : it.internalState.remaining = 0 →
      PlausibleStep it .done

@[always_inline, inline]
instance Take.instIterator [Monad m] [Iterator α m β] : Iterator (Take α m β) m β where
  IsPlausibleStep := Take.PlausibleStep
  step it :=
    match h : it.internalState.remaining with
    | 0 => pure <| .done (.depleted h)
    | k + 1 => do
      match ← it.internalState.inner.step with
      | .yield it' out h' => pure <| .yield (it'.take k) out (.yield h' h)
      | .skip it' h' => pure <| .skip (it'.take (k + 1)) (.skip h' h)
      | .done h' => pure <| .done (.done h')

def Take.Rel (m : Type w → Type w') [Monad m] [Iterator α m β] [Productive α m] :
    IterM (α := Take α m β) m β → IterM (α := Take α m β) m β → Prop :=
  InvImage (Prod.Lex Nat.lt_wfRel.rel IterM.TerminationMeasures.Productive.Rel)
    (fun it => (it.internalState.remaining, it.internalState.inner.finitelyManySkips))

theorem Take.rel_of_remaining [Monad m] [Iterator α m β] [Productive α m]
    {it it' : IterM (α := Take α m β) m β}
    (h : it'.internalState.remaining < it.internalState.remaining) : Take.Rel m it' it :=
  Prod.Lex.left _ _ h

theorem Take.rel_of_inner [Monad m] [Iterator α m β] [Productive α m] {remaining : Nat}
    {it it' : IterM (α := α) m β}
    (h : it'.finitelyManySkips.Rel it.finitelyManySkips) :
    Take.Rel m (it'.take remaining) (it.take remaining) :=
  Prod.Lex.right _ h

private def Take.instFinitenessRelation [Monad m] [Iterator α m β]
    [Productive α m] :
    FinitenessRelation (Take α m β) m where
  rel := Take.Rel m
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact WellFoundedRelation.wf
    · exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    cases h'
    case yield it' out k h' h'' =>
      cases h
      apply rel_of_remaining
      simp_all [IterM.take]
    case skip it' out k h' h'' =>
      cases h
      obtain ⟨it, k, rfl⟩ := IterM.take.surjective it
      cases h''
      apply Take.rel_of_inner
      exact IterM.TerminationMeasures.Productive.rel_of_skip h'
    case done _ =>
      cases h
    case depleted _ =>
      cases h

instance Take.instFinite [Monad m] [Iterator α m β] [Productive α m] :
    Finite (Take α m β) m :=
  Finite.of_finitenessRelation instFinitenessRelation

instance Take.instIteratorCollect [Monad m] [Monad n] [Iterator α m β] [Productive α m] :
    IteratorCollect (Take α m β) m n :=
  .defaultImplementation

instance Take.instIteratorCollectPartial [Monad m] [Monad n] [Iterator α m β] :
    IteratorCollectPartial (Take α m β) m n :=
  .defaultImplementation

instance Take.instIteratorLoop [Monad m] [Monad n] [Iterator α m β]
    [IteratorLoop α m n] [MonadLiftT m n] :
    IteratorLoop (Take α m β) m n :=
  .defaultImplementation

instance Take.instIteratorLoopPartial [Monad m] [Monad n] [Iterator α m β]
    [IteratorLoopPartial α m n] [MonadLiftT m n] :
    IteratorLoopPartial (Take α m β) m n :=
  .defaultImplementation

instance {α : Type w} [Monad m] [Iterator α m β] [Finite α m] [IteratorLoop α m m] :
    IteratorSize (Take α m β) m :=
  .defaultImplementation

instance {α : Type w} [Monad m] [Iterator α m β] [IteratorLoopPartial α m m] :
    IteratorSizePartial (Take α m β) m :=
  .defaultImplementation

end Std.Iterators
