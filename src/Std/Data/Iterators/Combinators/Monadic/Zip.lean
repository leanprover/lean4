/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Option.Lemmas
public import Init.Data.Iterators.Consumers.Loop
public import Init.Data.Iterators.Internal.Termination
import Init.Control.Lawful.MonadAttach.Lemmas

@[expose] public section

/-!

# Monadic `zip` combinator

This file provides an iterator combinator `IterM.zip` that combines two iterators into an iterator
of pairs.
-/

namespace Std.Iterators
open Std.Internal

variable {m : Type w → Type w'} [MonadAttach m]
  {α₁ : Type w} {β₁ : Type w} [Iterator α₁ m β₁]
  {α₂ : Type w} {β₂ : Type w} [Iterator α₂ m β₂]

/--
Internal state of the `zip` combinator. Do not depend on its internals.
-/
@[unbox]
structure Zip (α₁ : Type w) (m : Type w → Type w') {β₁ : Type w} [MonadAttach m] [Iterator α₁ m β₁]
    (α₂ : Type w) (β₂ : Type w) where
  left : IterM (α := α₁) m β₁
  memoizedLeft : (Option { out : β₁ // ∃ it : IterM (α := α₁) m β₁, it.IsPlausibleOutput out })
  right : IterM (α := α₂) m β₂

instance Zip.instIterator [Monad m] :
    Iterator (Zip α₁ m α₂ β₂) m (β₁ × β₂) where
  step it :=
    match it.internalState.memoizedLeft with
    | none => do
      match ← MonadAttach.attach it.internalState.left.step with
      | ⟨.yield it₁' out, hp⟩ =>
          return .skip ⟨⟨it₁', (some ⟨out, _, _, hp⟩), it.internalState.right⟩⟩
      | ⟨.skip it₁', _⟩ => return .skip ⟨⟨it₁', none, it.internalState.right⟩⟩
      | ⟨.done, _⟩ => return .done
    | some out₁ => do
      match ← it.internalState.right.step with
      | .yield it₂' out₂ =>
          return .yield ⟨⟨it.internalState.left, none, it₂'⟩⟩ (out₁, out₂)
      | .skip it₂' => return .skip ⟨⟨it.internalState.left, (some out₁), it₂'⟩⟩
      | .done => return .done

/--
Given two iterators `left` and `right`, `left.zip right` is an iterator that yields pairs of
outputs of `left` and `right`. When one of them terminates,
the `zip` iterator will also terminate.

**Marble diagram:**

```text
left               --a        ---b        --c
right                 --x         --y        --⊥
left.zip right     -----(a, x)------(b, y)-----⊥
```

**Termination properties:**

* `Finite` instance: only if either `left` or `right` is finite and the other is productive
* `Productive` instance: only if `left` and `right` are productive

There are situations where `left.zip right` is finite (or productive) but none of the instances
above applies. For example, if the computation happens in an `Except` monad and `left` immediately
fails when calling `step`, then `left.zip right` will also do so. In such a case, the `Finite`
(or `Productive`) instance needs to be proved manually.

**Performance:**

This combinator incurs an additional O(1) cost with each step taken by `left` or `right`.

Right now, the compiler does not unbox the internal state, leading to worse performance than
possible.
-/
@[always_inline, inline]
def IterM.zip
    (left : IterM (α := α₁) m β₁) (right : IterM (α := α₂) m β₂) :
    IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂) :=
  toIterM ⟨left, none, right⟩ m _

variable (m) in
def Zip.Rel₁ [Finite α₁ m] [Productive α₂ m] :
    IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂) → IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂) → Prop :=
  InvImage (Prod.Lex
      IterM.TerminationMeasures.Finite.Rel
      (Prod.Lex (Option.lt emptyRelation) IterM.TerminationMeasures.Productive.Rel))
    (fun it => (it.internalState.left.finitelyManySteps, (it.internalState.memoizedLeft, it.internalState.right.finitelyManySkips)))

theorem Zip.rel₁_of_left [Finite α₁ m] [Productive α₂ m] {it' it : IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂)}
    (h : it'.internalState.left.finitelyManySteps.Rel it.internalState.left.finitelyManySteps) :
    Zip.Rel₁ m it' it :=
  Prod.Lex.left _ _ h

theorem Zip.rel₁_of_memoizedLeft [Finite α₁ m] [Productive α₂ m]
    {left : IterM (α := α₁) m β₁} {b' b} {right' right : IterM (α := α₂) m β₂}
    (h : Option.lt emptyRelation b' b) :
    Zip.Rel₁ m ⟨left, b', right'⟩ ⟨left, b, right⟩ :=
  Prod.Lex.right _ <| Prod.Lex.left _ _ h

theorem Zip.rel₁_of_right [Finite α₁ m] [Productive α₂ m]
    {left : IterM (α := α₁) m β₁} {b b' : _} {it' it : IterM (α := α₂) m β₂}
    (h : b' = b)
    (h' : it'.finitelyManySkips.Rel it.finitelyManySkips) :
    Zip.Rel₁ m ⟨left, b', it'⟩ ⟨left, b, it⟩ := by
  cases h
  exact Prod.Lex.right _ <| Prod.Lex.right _ h'

def Zip.instFinitenessRelation₁
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Finite α₁ m] [Productive α₂ m] :
    FinitenessRelation (Zip α₁ m α₂ β₂) m where
  rel := Zip.Rel₁ m
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact WellFoundedRelation.wf
    · refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
      · apply Option.wellFounded_lt
        exact emptyWf.wf
      · exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, hs, h⟩ := h
    simp only [IterM.IsPlausibleStep, Iterator.step] at h
    split at h
    · obtain ⟨step', hs', h⟩ := LawfulMonadAttach.canReturn_bind_imp' h
      cases step' using PlausibleIterStep.casesOn
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        cases hs
        apply Zip.rel₁_of_left
        exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        cases hs
        apply Zip.rel₁_of_left
        exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        nomatch hs
    · obtain ⟨step', hs', h⟩ := LawfulMonadAttach.canReturn_bind_imp' h
      cases step', hs' using PlausibleIterStep.casesOn'
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        cases hs
        apply Zip.rel₁_of_memoizedLeft
        simp [Option.lt, *]
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        cases hs
        apply Zip.rel₁_of_right
        · simp_all
        · exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        nomatch hs

instance Zip.instFinite₁
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Finite α₁ m] [Productive α₂ m] :
    Finite (Zip α₁ m α₂ β₂) m :=
  Finite.of_finitenessRelation Zip.instFinitenessRelation₁

variable (m) in
def Zip.Rel₂ [Productive α₁ m] [Finite α₂ m] :
    IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂) → IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂) → Prop :=
  InvImage (Prod.Lex
      IterM.TerminationMeasures.Finite.Rel
      (Prod.Lex (Option.SomeLtNone.lt emptyRelation) IterM.TerminationMeasures.Productive.Rel))
    (fun it => (it.internalState.right.finitelyManySteps, (it.internalState.memoizedLeft, it.internalState.left.finitelyManySkips)))

theorem Zip.rel₂_of_right [Productive α₁ m] [Finite α₂ m] {it' it : IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂)}
    (h : it'.internalState.right.finitelyManySteps.Rel it.internalState.right.finitelyManySteps) : Zip.Rel₂ m it' it :=
  Prod.Lex.left _ _ h

theorem Zip.rel₂_of_memoizedLeft [Productive α₁ m] [Finite α₂ m]
    {right : IterM (α := α₂) m β₂} {b' b} {left' left : IterM (α := α₁) m β₁}
    (h : Option.SomeLtNone.lt emptyRelation b' b) :
    Zip.Rel₂ m ⟨left, b', right⟩ ⟨left', b, right⟩ :=
  Prod.Lex.right _ <| Prod.Lex.left _ _ h

theorem Zip.rel₂_of_left [Productive α₁ m] [Finite α₂ m]
    {right : IterM (α := α₂) m β₂} {b b' : _} {it' it : IterM (α := α₁) m β₁}
    (h : b' = b)
    (h' : it'.finitelyManySkips.Rel it.finitelyManySkips) :
    Zip.Rel₂ m ⟨it', b', right⟩ ⟨it, b, right⟩ := by
  cases h
  exact Prod.Lex.right _ <| Prod.Lex.right _ h'

def Zip.instFinitenessRelation₂
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Productive α₁ m] [Finite α₂ m] :
    FinitenessRelation (Zip α₁ m α₂ β₂) m where
  rel := Zip.Rel₂ m
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact WellFoundedRelation.wf
    · refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
      · apply Option.SomeLtNone.wellFounded_lt
        exact emptyWf.wf
      · exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, hs, h⟩ := h
    simp only [IterM.IsPlausibleStep, Iterator.step] at h
    split at h
    · obtain ⟨step', hs', h⟩ := LawfulMonadAttach.canReturn_bind_imp' h
      cases step' using PlausibleIterStep.casesOn
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        cases hs
        apply Zip.rel₂_of_memoizedLeft
        simp_all [Option.SomeLtNone.lt]
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        cases hs
        apply Zip.rel₂_of_left
        · simp_all
        · exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        nomatch hs
    · obtain ⟨step', hs', h⟩ := LawfulMonadAttach.canReturn_bind_imp' h
      cases step', hs' using PlausibleIterStep.casesOn'
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        cases hs
        apply Zip.rel₂_of_right
        exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        cases hs
        apply Zip.rel₂_of_right
        exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        nomatch hs

instance Zip.instFinite₂
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Productive α₁ m] [Finite α₂ m] :
    Finite (Zip α₁ m α₂ β₂) m :=
  Finite.of_finitenessRelation Zip.instFinitenessRelation₂

variable (m) in
def Zip.Rel₃ [Productive α₁ m] [Productive α₂ m] :
    IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂) → IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂) → Prop :=
  InvImage (Prod.Lex
      (Option.SomeLtNone.lt emptyRelation)
      (Prod.Lex (IterM.TerminationMeasures.Productive.Rel) IterM.TerminationMeasures.Productive.Rel))
    (fun it => (it.internalState.memoizedLeft, (it.internalState.left.finitelyManySkips, it.internalState.right.finitelyManySkips)))

theorem Zip.rel₃_of_memoizedLeft [Productive α₁ m] [Productive α₂ m] {it' it : IterM (α := Zip α₁ m α₂ β₂) m (β₁ × β₂)}
    (h : Option.SomeLtNone.lt emptyRelation it'.internalState.memoizedLeft it.internalState.memoizedLeft) :
    Zip.Rel₃ m it' it :=
  Prod.Lex.left _ _ h

theorem Zip.rel₃_of_left [Productive α₁ m] [Productive α₂ m]
    {left' left : IterM (α := α₁) m β₁} {b} {right' right : IterM (α := α₂) m β₂}
    (h : left'.finitelyManySkips.Rel left.finitelyManySkips) :
    Zip.Rel₃ m ⟨left', b, right'⟩ ⟨left, b, right⟩ :=
  Prod.Lex.right _ <| Prod.Lex.left _ _ h

theorem Zip.rel₃_of_right [Productive α₁ m] [Productive α₂ m]
    {left : IterM (α := α₁) m β₁} {b b' : _} {it' it : IterM (α := α₂) m β₂}
    (h : b' = b)
    (h' : it'.finitelyManySkips.Rel it.finitelyManySkips) :
    Zip.Rel₃ m ⟨left, b', it'⟩ ⟨left, b, it⟩ := by
  cases h
  exact Prod.Lex.right _ <| Prod.Lex.right _ h'

def Zip.instProductivenessRelation
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Productive α₁ m] [Productive α₂ m] :
    ProductivenessRelation (Zip α₁ m α₂ β₂) m where
  rel := Zip.Rel₃ m
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · apply Option.SomeLtNone.wellFounded_lt
      exact emptyWf.wf
    · refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
      · exact WellFoundedRelation.wf
      · exact WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp only [IterM.IsPlausibleSkipSuccessorOf, IterM.IsPlausibleStep, Iterator.step] at h
    split at h <;> rename_i heq
    · obtain ⟨step, hs, h⟩ := LawfulMonadAttach.canReturn_bind_imp' h
      cases step using PlausibleIterStep.casesOn
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        apply Zip.rel₃_of_memoizedLeft
        simp [Option.SomeLtNone.lt, *]
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        obtain ⟨⟨left, memoizedLeft, right⟩⟩ := it
        cases heq
        apply Zip.rel₃_of_left
        exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›
      · nomatch LawfulMonadAttach.eq_of_canReturn_pure h
    · obtain ⟨step, hs, h⟩ := LawfulMonadAttach.canReturn_bind_imp' h
      cases step, hs using PlausibleIterStep.casesOn'
      · nomatch LawfulMonadAttach.eq_of_canReturn_pure h
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        apply Zip.rel₃_of_right
        · simp_all
        · exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›
      · nomatch LawfulMonadAttach.eq_of_canReturn_pure h

instance Zip.instProductive
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Productive α₁ m] [Productive α₂ m] :
    Productive (Zip α₁ m α₂ β₂) m :=
  Productive.of_productivenessRelation Zip.instProductivenessRelation

instance Zip.instIteratorCollect [Monad m] [Monad n] :
    IteratorCollect (Zip α₁ m α₂ β₂) m n :=
  .defaultImplementation

instance Zip.instIteratorLoop [Monad m] [Monad n] [MonadAttach n] :
    IteratorLoop (Zip α₁ m α₂ β₂) m n :=
  .defaultImplementation

end Std.Iterators
