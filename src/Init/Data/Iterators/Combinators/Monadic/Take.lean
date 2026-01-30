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

@[expose] public section

/-!
This module provides the iterator combinator `IterM.take`.
-/

namespace Std

variable {α : Type w} {m : Type w → Type w'} {β : Type w}

/--
The internal state of the `IterM.take` iterator combinator.
-/
@[unbox]
structure Iterators.Types.Take (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β] where
  /--
  Internal implementation detail of the iterator library.
  Caution: For `take n`, `countdown` is `n + 1`.
  If `countdown` is zero, the combinator only terminates when `inner` terminates.
  -/
  countdown : Nat
  /-- Internal implementation detail of the iterator library -/
  inner : IterM (α := α) m β
  /--
  Internal implementation detail of the iterator library.
  This proof term ensures that a `take` always produces a finite iterator from a productive one.
  -/
  finite : countdown > 0 ∨ Finite α m

open Std.Iterators Std.Iterators.Types

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
def IterM.take [Iterator α m β] (n : Nat) (it : IterM (α := α) m β) :=
  IterM.mk (Take.mk (n + 1) it (Or.inl <| Nat.zero_lt_succ _)) m β

/--
This combinator is only useful for advanced use cases.

Given a finite iterator `it`, returns an iterator that behaves exactly like `it` but is of the same
type as `it.take n`.

**Marble diagram:**

```text
it          ---a----b---c--d-e--⊥
it.toTake   ---a----b---c--d-e--⊥
```

**Termination properties:**

* `Finite` instance: always
* `Productive` instance: always

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it`.
-/
@[always_inline, inline]
def IterM.toTake [Iterator α m β] [Finite α m] (it : IterM (α := α) m β) :=
  IterM.mk (Take.mk 0 it (Or.inr inferInstance)) m β

theorem IterM.take.surjective_of_zero_lt {α : Type w} {m : Type w → Type w'} {β : Type w}
    [Iterator α m β] (it : IterM (α := Take α m) m β) (h : 0 < it.internalState.countdown) :
    ∃ (it₀ : IterM (α := α) m β) (k : Nat), it = it₀.take k := by
  refine ⟨it.internalState.inner, it.internalState.countdown - 1, ?_⟩
  simp only [take, Nat.sub_add_cancel (m := 1) (n := it.internalState.countdown) (by omega)]
  rfl

namespace Iterators.Types

inductive Take.PlausibleStep [Iterator α m β] (it : IterM (α := Take α m) m β) :
    (step : IterStep (IterM (α := Take α m) m β) β) → Prop where
  | yield : ∀ {it' out}, it.internalState.inner.IsPlausibleStep (.yield it' out) →
      (h : it.internalState.countdown ≠ 1) → PlausibleStep it (.yield ⟨it.internalState.countdown - 1, it', it.internalState.finite.imp_left (by omega)⟩ out)
  | skip : ∀ {it'}, it.internalState.inner.IsPlausibleStep (.skip it') →
      it.internalState.countdown ≠ 1 → PlausibleStep it (.skip ⟨it.internalState.countdown, it', it.internalState.finite⟩)
  | done : it.internalState.inner.IsPlausibleStep .done → PlausibleStep it .done
  | depleted : it.internalState.countdown = 1 →
      PlausibleStep it .done

@[always_inline, inline]
instance Take.instIterator [Monad m] [Iterator α m β] : Iterator (Take α m) m β where
  IsPlausibleStep := Take.PlausibleStep
  step it :=
    if h : it.internalState.countdown = 1 then
      pure <| .deflate <| .done (.depleted h)
    else do
      match (← it.internalState.inner.step).inflate with
      | .yield it' out h' =>
        pure <| .deflate <| .yield ⟨it.internalState.countdown - 1, it', (it.internalState.finite.imp_left (by omega))⟩ out (.yield h' h)
      | .skip it' h' => pure <| .deflate <| .skip ⟨it.internalState.countdown, it', it.internalState.finite⟩ (.skip h' h)
      | .done h' => pure <| .deflate <| .done (.done h')

def Take.Rel (m : Type w → Type w') [Monad m] [Iterator α m β] [Productive α m] :
    IterM (α := Take α m) m β → IterM (α := Take α m) m β → Prop :=
  open scoped Classical in
  if _ : Finite α m then
    InvImage (Prod.Lex Nat.lt_wfRel.rel IterM.TerminationMeasures.Finite.Rel)
      (fun it => (it.internalState.countdown, it.internalState.inner.finitelyManySteps))
  else
    InvImage (Prod.Lex Nat.lt_wfRel.rel IterM.TerminationMeasures.Productive.Rel)
      (fun it => (it.internalState.countdown, it.internalState.inner.finitelyManySkips))

theorem Take.rel_of_countdown [Monad m] [Iterator α m β] [Productive α m]
    {it it' : IterM (α := Take α m) m β}
    (h : it'.internalState.countdown < it.internalState.countdown) : Take.Rel m it' it := by
  simp only [Rel]
  split <;> exact Prod.Lex.left _ _ h

theorem Take.rel_of_inner [Monad m] [Iterator α m β] [Productive α m] {remaining : Nat}
    {it it' : IterM (α := α) m β}
    (h : it'.finitelyManySkips.Rel it.finitelyManySkips) :
    Take.Rel m (it'.take remaining) (it.take remaining) := by
  simp only [Rel]
  split
  · exact Prod.Lex.right _ (.of_productive h)
  · exact Prod.Lex.right _ h

theorem Take.rel_of_zero_of_inner [Monad m] [Iterator α m β]
    {it it' : IterM (α := Take α m) m β}
    (h : it.internalState.countdown = 0) (h' : it'.internalState.countdown = 0)
    (h'' : haveI := it.internalState.finite.resolve_left (by omega); it'.internalState.inner.finitelyManySteps.Rel it.internalState.inner.finitelyManySteps) :
    haveI := it.internalState.finite.resolve_left (by omega)
    Take.Rel m it' it := by
  haveI := it.internalState.finite.resolve_left (by omega)
  simp only [Rel, this, ↓reduceDIte, InvImage, h, h']
  exact Prod.Lex.right _ h''

private def Take.instFinitenessRelation [Monad m] [Iterator α m β]
    [Productive α m] :
    FinitenessRelation (Take α m) m where
  Rel := Take.Rel m
  wf := by
    rw [Rel]
    split
    all_goals
      apply InvImage.wf
      refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
      · exact WellFoundedRelation.wf
      · exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    cases h'
    case yield it' out k h' h'' =>
      cases h
      cases it.internalState.finite
      · apply rel_of_countdown
        simp only
        omega
      · by_cases h : it.internalState.countdown = 0
        · simp only [h, Nat.zero_le, Nat.sub_eq_zero_of_le]
          apply rel_of_zero_of_inner h rfl
          exact .single ⟨_, rfl, h'⟩
        · apply rel_of_countdown
          simp only
          omega
    case skip it' out k h' h'' =>
      cases h
      by_cases h : it.internalState.countdown = 0
      · simp only [h]
        apply Take.rel_of_zero_of_inner h rfl
        exact .single ⟨_, rfl, h'⟩
      · obtain ⟨it, k, rfl⟩ := IterM.take.surjective_of_zero_lt it (by omega)
        apply Take.rel_of_inner
        exact IterM.TerminationMeasures.Productive.rel_of_skip h'
    case done _ =>
      cases h
    case depleted _ =>
      cases h

instance Take.instFinite [Monad m] [Iterator α m β] [Productive α m] :
    Finite (Take α m) m :=
  by exact Finite.of_finitenessRelation instFinitenessRelation

instance Take.instIteratorLoop {n : Type x → Type x'} [Monad m] [Monad n] [Iterator α m β] :
    IteratorLoop (Take α m) m n :=
  .defaultImplementation

end Std.Iterators.Types
