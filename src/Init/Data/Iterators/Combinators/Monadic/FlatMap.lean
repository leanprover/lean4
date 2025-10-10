/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Basic
public import Init.Data.Iterators.Consumers.Collect
public import Init.Data.Iterators.Consumers.Loop
public import Init.Data.Iterators.Combinators.Monadic.FilterMap
public import Init.Data.Iterators.PostconditionMonad
public import Init.Data.Iterators.Internal.Termination
public import Init.Data.Option.Lemmas

public import Std.Data.Iterators.Producers.List

set_option doc.verso true

/-!
# Monadic {lit}`flatMap` combinator

This file provides the {lit}`flatMap` iterator and variants of it.

If `it` is any iterator, `it.flatMap f` maps each output of `it` to an iterator using `f`.
The `flatMap` first emits all outputs of the first iterator, then of the second, and so on.
In other words, `it` flattens the iterator of iterators obtained by mapping with `f`.

Several variants of `flatMap` are provided:

* `M` suffix: monadic mapping function that can have side effects
* `D` suffix: dependently typed mapping function
-/

namespace Std.Iterators

@[ext, unbox]
public structure Flatten (α α₂ β : Type w) (m) where
  it₁ : IterM (α := α) m (IterM (α := α₂) m β)
  it₂ : Option (IterM (α := α₂) m β)

@[always_inline]
def IterM.flattenAfter {α α₂ β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β]
    (it₁ : IterM (α := α) m (IterM (α := α₂) m β)) (it₂ : Option (IterM (α := α₂) m β)) :=
  (toIterM (α := Flatten α α₂ β m) ⟨it₁, it₂⟩ m β : IterM m β)

@[always_inline]
public def IterM.flatMapAfterM {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β] [Iterator α₂ m γ]
    (f : β → m (IterM (α := α₂) m γ)) (it₁ : IterM (α := α) m β) (it₂ : Option (IterM (α := α₂) m γ)) :=
  ((it₁.mapM f).flattenAfter it₂ : IterM m γ)

@[always_inline, expose]
public def IterM.flatMapM {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β] [Iterator α₂ m γ]
    (f : β → m (IterM (α := α₂) m γ)) (it : IterM (α := α) m β) :=
  (it.flatMapAfterM f none : IterM m γ)

@[always_inline]
public def IterM.flatMapAfter {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β] [Iterator α₂ m γ]
    (f : β → IterM (α := α₂) m γ) (it₁ : IterM (α := α) m β) (it₂ : Option (IterM (α := α₂) m γ)) :=
  ((it₁.map f).flattenAfter it₂ : IterM m γ)

@[always_inline, expose]
public def IterM.flatMap {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β] [Iterator α₂ m γ]
    (f : β → IterM (α := α₂) m γ) (it : IterM (α := α) m β) :=
  (it.flatMapAfter f none : IterM m γ)

variable {α α₂ β : Type w} {m : Type w → Type w'}

public inductive Flatten.IsPlausibleStep [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β] :
    (it : IterM (α := Flatten α α₂ β m) m β) → (step : IterStep (IterM (α := Flatten α α₂ β m) m β) β) → Prop where
  | outerYield : ∀ {it₁ it₁' it₂'}, it₁.IsPlausibleStep (.yield it₁' it₂') →
      IsPlausibleStep (toIterM ⟨it₁, none⟩ m β) (.skip (toIterM ⟨it₁', some it₂'⟩ m β))
  | outerSkip : ∀ {it₁ it₁'}, it₁.IsPlausibleStep (.skip it₁') →
      IsPlausibleStep (toIterM ⟨it₁, none⟩ m β) (.skip (toIterM ⟨it₁', none⟩ m β))
  | outerDone : ∀ {it₁}, it₁.IsPlausibleStep .done →
      IsPlausibleStep (toIterM ⟨it₁, none⟩ m β) .done
  | innerYield : ∀ {it₁ it₂ it₂' b}, it₂.IsPlausibleStep (.yield it₂' b) →
      IsPlausibleStep (toIterM ⟨it₁, some it₂⟩ m β) (.yield (toIterM ⟨it₁, some it₂'⟩ m β) b)
  | innerSkip : ∀ {it₁ it₂ it₂'}, it₂.IsPlausibleStep (.skip it₂') →
      IsPlausibleStep (toIterM ⟨it₁, some it₂⟩ m β) (.skip (toIterM ⟨it₁, some it₂'⟩ m β))
  | innerDone : ∀ {it₁ it₂}, it₂.IsPlausibleStep .done →
      IsPlausibleStep (toIterM ⟨it₁, some it₂⟩ m β) (.skip (toIterM ⟨it₁, none⟩ m β))

public instance Flatten.instIterator [Monad m] [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β] :
    Iterator (Flatten α α₂ β m) m β where
  IsPlausibleStep := IsPlausibleStep
  step it :=
    match it with
    | ⟨it₁, none⟩ => do
      match ← it₁.step with
      | .yield it₁' it₂' h =>
          pure <| .skip ⟨it₁', some it₂'⟩ (.outerYield h)
      | .skip it₁' h =>
          pure <| .skip ⟨it₁', none⟩ (.outerSkip h)
      | .done h =>
          pure <| .done (.outerDone h)
    | ⟨it₁, some it₂⟩ => do
      match ← it₂.step with
      | .yield it₂' c h =>
          pure <| .yield ⟨it₁, some it₂'⟩ c (.innerYield h)
      | .skip it₂' h =>
          pure <| .skip ⟨it₁, some it₂'⟩ (.innerSkip h)
      | .done h =>
          pure <| .skip ⟨it₁, none⟩ (.innerDone h)

section Finite

variable {α : Type w} {α₂ : Type w} {β : Type w} {m : Type w → Type w'}

variable (α m β) in
def Rel [Monad m] [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β] [Finite α m] [Finite α₂ m] :
    IterM (α := Flatten α α₂ β m) m β → IterM (α := Flatten α α₂ β m) m β → Prop :=
  InvImage
    (Prod.Lex
      (InvImage IterM.TerminationMeasures.Finite.Rel IterM.finitelyManySteps)
      (Option.lt (InvImage IterM.TerminationMeasures.Finite.Rel IterM.finitelyManySteps)))
    (fun it => (it.internalState.it₁, it.internalState.it₂))

theorem Flatten.rel_of_left [Monad m] [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β]
    [Finite α m] [Finite α₂ m] {it it'}
    (h : it'.internalState.it₁.finitelyManySteps.Rel it.internalState.it₁.finitelyManySteps) :
    Rel α β m it' it :=
  Prod.Lex.left _ _ h

theorem Flatten.rel_of_right₁ [Monad m] [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β]
    [Finite α m] [Finite α₂ m] {it₁ it₂ it₂'}
    (h : (InvImage IterM.TerminationMeasures.Finite.Rel IterM.finitelyManySteps) it₂' it₂) :
    Rel α β m ⟨it₁, some it₂'⟩ ⟨it₁, some it₂⟩ := by
  refine Prod.Lex.right _ h

theorem Flatten.rel_of_right₂ [Monad m] [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β]
    [Finite α m] [Finite α₂ m] {it₁ it₂} :
    Rel α β m ⟨it₁, none⟩ ⟨it₁, some it₂⟩ :=
  Prod.Lex.right _ True.intro

instance [Monad m] [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β]
    [Finite α m] [Finite α₂ m] :
    FinitenessRelation (Flatten α α₂ β m) m where
  rel := Rel α β m
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact InvImage.wf _ WellFoundedRelation.wf
    · exact Option.wellFounded_lt <| InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    cases h' <;> cases h
    case outerYield =>
      apply Flatten.rel_of_left
      exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
    case outerSkip =>
      apply Flatten.rel_of_left
      exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›
    case innerYield =>
      apply Flatten.rel_of_right₁
      exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
    case innerSkip =>
      apply Flatten.rel_of_right₁
      exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›
    case innerDone =>
      apply Flatten.rel_of_right₂

@[no_expose]
public instance [Monad m] [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β]
    [Finite α m] [Finite α₂ m] : Finite (Flatten α α₂ β m) m :=
  .of_finitenessRelation instFinitenessRelationFlattenOfIterMOfFinite

end Finite

section Productive

variable {α : Type w} {α₂ : Type w} {β : Type w} {m : Type w → Type w'}

variable (α m β) in
def ProductiveRel [Monad m] [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β] [Finite α m]
    [Productive α₂ m] :
    IterM (α := Flatten α α₂ β m) m β → IterM (α := Flatten α α₂ β m) m β → Prop :=
  InvImage
    (Prod.Lex
      (InvImage IterM.TerminationMeasures.Finite.Rel IterM.finitelyManySteps)
      (Option.lt (InvImage IterM.TerminationMeasures.Productive.Rel IterM.finitelyManySkips)))
    (fun it => (it.internalState.it₁, it.internalState.it₂))

theorem Flatten.productiveRel_of_left [Monad m] [Iterator α m (IterM (α := α₂) m β)]
    [Iterator α₂ m β] [Finite α m] [Productive α₂ m] {it it'}
    (h : it'.internalState.it₁.finitelyManySteps.Rel it.internalState.it₁.finitelyManySteps) :
    ProductiveRel α β m it' it :=
  Prod.Lex.left _ _ h

theorem Flatten.productiveRel_of_right₁ [Monad m] [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β]
    [Finite α m] [Productive α₂ m] {it₁ it₂ it₂'}
    (h : (InvImage IterM.TerminationMeasures.Productive.Rel IterM.finitelyManySkips) it₂' it₂) :
    ProductiveRel α β m ⟨it₁, some it₂'⟩ ⟨it₁, some it₂⟩ := by
  refine Prod.Lex.right _ h

theorem Flatten.productiveRel_of_right₂ [Monad m] [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β]
    [Finite α m] [Productive α₂ m] {it₁ it₂} :
    ProductiveRel α β m ⟨it₁, none⟩ ⟨it₁, some it₂⟩ :=
  Prod.Lex.right _ True.intro

instance [Monad m] [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β]
    [Finite α m] [Productive α₂ m] :
    ProductivenessRelation (Flatten α α₂ β m) m where
  rel := ProductiveRel α β m
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact InvImage.wf _ WellFoundedRelation.wf
    · exact Option.wellFounded_lt <| InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    cases h
    case outerYield =>
      apply Flatten.productiveRel_of_left
      exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
    case outerSkip =>
      apply Flatten.productiveRel_of_left
      exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›
    case innerSkip =>
      apply Flatten.productiveRel_of_right₁
      exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›
    case innerDone =>
      apply Flatten.productiveRel_of_right₂

@[no_expose]
public instance [Monad m] [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β]
    [Finite α m] [Productive α₂ m] : Productive (Flatten α α₂ β m) m :=
  .of_productivenessRelation instProductivenessRelationFlattenOfFiniteIterMOfProductive

end Productive

public instance Flatten.instIteratorCollect [Monad m] [Monad n] [Iterator α m (IterM (α := α₂) m β)]
    [Iterator α₂ m β] : IteratorCollect (Flatten α α₂ β m) m n :=
  .defaultImplementation

public instance Flatten.instIteratorCollectPartial [Monad m] [Monad n] [Iterator α m (IterM (α := α₂) m β)]
    [Iterator α₂ m β] : IteratorCollectPartial (Flatten α α₂ β m) m n :=
  .defaultImplementation

public instance Flatten.instIteratorLoop [Monad m] [Monad n] [Iterator α m (IterM (α := α₂) m β)]
    [Iterator α₂ m β] : IteratorLoop (Flatten α α₂ β m) m n :=
  .defaultImplementation

public instance Flatten.instIteratorLoopPartial [Monad m] [Monad n] [Iterator α m (IterM (α := α₂) m β)]
    [Iterator α₂ m β] : IteratorLoopPartial (Flatten α α₂ β m) m n :=
  .defaultImplementation

end Std.Iterators
