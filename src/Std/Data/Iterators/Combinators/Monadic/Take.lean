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
import Std.Data.Iterators.Workbench.Termination

/-!
This module provides the iterator combinator `IterM.take`.
-/

namespace Std.Iterators

variable {α : Type w} {m : Type w → Type w'} {β : Type w}

structure Take (α : Type w) (m : Type w → Type w') (β : Type w) where
  remaining : Nat
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

* `Finite` instance: always ✓
* `Productive` instance: only if `it` is productive

_TODO_: prove `Productive`

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it`.
-/
@[inline]
def IterM.take (n : Nat) (it : IterM (α := α) m β) :=
  toIterM (Take.mk n it) m β

theorem IterM.take.surjective {α : Type w} {m : Type w → Type w'} {β : Type w}
    (it : IterM (α := Take α m β) m β) :
    ∃ (it₀ : IterM (α := α) m β) (k : Nat), it = it₀.take k := by
  refine ⟨it.internalState.inner, it.internalState.remaining, rfl⟩

inductive Take.PlausibleStep [Iterator α m β] (it : IterM (α := Take α m β) m β) :
    (step : IterStep (IterM (α := Take α m β) m β) β) → Prop where
  | yield : ∀ {it' out k}, it.internalState.inner.plausible_step (.yield it' out) →
      it.internalState.remaining = k + 1 → PlausibleStep it (.yield (it'.take k) out)
  | skip : ∀ {it' k}, it.internalState.inner.plausible_step (.skip it') →
      it.internalState.remaining = k + 1 → PlausibleStep it (.skip (it'.take (k + 1)))
  | done : it.internalState.inner.plausible_step .done → PlausibleStep it .done
  | depleted : it.internalState.remaining = 0 →
      PlausibleStep it .done

instance Take.instIterator [Monad m] [Iterator α m β] : Iterator (Take α m β) m β where
  plausible_step := Take.PlausibleStep
  step it :=
    match h : it.internalState.remaining with
    | 0 => pure <| .done (.depleted h)
    | k + 1 => do
      match ← it.internalState.inner.step with
      | .yield it' out h' => pure <| .yield (it'.take k) out (.yield h' h)
      | .skip it' h' => pure <| .skip (it'.take (k + 1)) (.skip h' h)
      | .done h' => pure <| .done (.done h')

def Take.rel (m : Type w → Type w') [Monad m] [Iterator α m β] [Productive α m] :
    IterM (α := Take α m β) m β → IterM (α := Take α m β) m β → Prop :=
  InvImage (Prod.Lex Nat.lt_wfRel.rel IterM.TerminationMeasures.Productive.rel)
    (fun it => (it.internalState.remaining, it.internalState.inner.finitelyManySkips))

theorem Take.rel_of_remaining [Monad m] [Iterator α m β] [Productive α m]
    {it it' : IterM (α := Take α m β) m β}
    (h : it'.internalState.remaining < it.internalState.remaining) : Take.rel m it' it :=
  Prod.Lex.left _ _ h

theorem Take.rel_of_inner [Monad m] [Iterator α m β] [Productive α m] {remaining : Nat}
    {it it' : IterM (α := α) m β}
    (h : it'.finitelyManySkips.rel it.finitelyManySkips) :
    Take.rel m (it'.take remaining) (it.take remaining) :=
  Prod.Lex.right _ h

instance Take.instFinitenessRelation [Monad m] [Iterator α m β]
    [Productive α m] :
    FinitenessRelation (Take α m β) m where
  rel := Take.rel m
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

instance Take.instIteratorToArray [Monad m] [Iterator α m β] [Productive α m] :
    IteratorCollect (Take α m β) m :=
  .defaultImplementation

instance Take.instIteratorToArrayPartial [Monad m] [Iterator α m β] :
    IteratorCollectPartial (Take α m β) m :=
  .defaultImplementation

instance Take.instIteratorFor [Monad m] [Monad n] [Iterator α m β]
    [IteratorLoop α m n] [MonadLiftT m n] :
    IteratorLoop (Take α m β) m n where
  forIn lift {γ} Plausible wf it init f := by
    refine Prod.fst <$> IteratorLoop.forIn lift (γ := γ × Nat)
        (fun
          | out, (c, n), .yield (c', n') => n = n' + 1 ∧ Plausible out c (.yield c')
          | out, (c, n), .done (c', n') => True)
        (by
          simp only [IteratorLoop.WellFounded] at ⊢ wf
          letI : WellFoundedRelation _ := ⟨_, wf⟩
          apply Subrelation.wf (r := InvImage WellFoundedRelation.rel fun p => (p.1.take (p.2.2 + 1), p.2.1))
            (fun {p q} h => by
              simp only [InvImage, WellFoundedRelation.rel, this, IteratorLoop.rel, IterM.plausible_step,
                Iterator.plausible_step]
              obtain ⟨out, h, h'⟩ | ⟨h, h'⟩ := h
              · apply Or.inl
                exact ⟨out, .yield h (by simp only [IterM.take, internalState_toIterM,
                  Nat.add_right_cancel_iff, this]; exact h'.1), h'.2⟩
              · apply Or.inr
                refine ⟨?_, by rw [h']⟩
                rw [h']
                apply PlausibleStep.skip
                · exact h
                · rfl)
          apply InvImage.wf
          exact WellFoundedRelation.wf)
        it.internalState.inner
        (init, it.internalState.remaining)
        fun out acc =>
          match h : acc.snd with
          | 0 => pure <| ⟨.done acc, .intro⟩
          | n + 1 => (fun
              | ⟨.yield x, hp⟩ => ⟨.yield ⟨x, n⟩, by simp [h, hp]⟩
              | ⟨.done x ,hp⟩ => ⟨.done ⟨x, n⟩, .intro⟩) <$> f out acc.fst

instance Take.instIteratorForPartial [Monad m] [Monad n] [Iterator α m β]
    [IteratorLoopPartial α m n] [MonadLiftT m n] :
    IteratorLoopPartial (Take α m β) m n where
  forInPartial lift {γ} it init f := do
    Prod.fst <$> IteratorLoopPartial.forInPartial lift it.internalState.inner (γ := γ × Nat)
        (init, it.internalState.remaining)
        fun out acc =>
          match acc.snd with
          | 0 => pure <| .done acc
          | n + 1 => (fun | .yield x => .yield ⟨x, n⟩ | .done x => .done ⟨x, n⟩) <$> f out acc.fst

  -- TODO: use [IteratorFor α m n]
    -- forIn {γ} it init successor_of stepper _ := by
    -- refine Prod.fst <$> (IteratorFor.forIn (α := α) (m := m) (n := n) (innerIter it) (γ := γ × Nat) (init, it.inner.remaining)
    --   (successor_of := fun b c c' => c.snd = c'.snd + 1) ?_ ?_)
    -- · exact fun b c => do
    --     let result ← stepper b c.fst
    --     return match result.val with
    --     | .yield x => .yield ⟨
    --     | .done x => sorry
    -- refine Subrelation.wf (r := InvImage IterM.TerminationMeasures.Finite.rel (fun p => (p.1).finitelyManySteps)) ?_ ?_
    -- · intro p' p h
    --   cases h
    --   · apply IterM.plausible_successor_of_skip
    --     rename_i h
    --     exact h.1
    --   · rename_i h
    --     obtain ⟨out, h, _⟩ := h -- Interesting: Moving `obtain` after `apply` leads to failure
    --     apply IterM.plausible_successor_of_yield
    --     exact h

end Std.Iterators
