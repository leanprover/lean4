/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Combinators.Monadic.FilterMap
public import Init.Data.Option.Lemmas
import Init.Control.Lawful.MonadAttach.Lemmas

/-!
# Monadic `flatMap` combinator

This file provides the `flatMap` iterator combinator and variants of it.

If `it` is any iterator, `it.flatMap f` maps each output of `it` to an iterator using
`f`.

`it.flatMap f` first emits all outputs of the first obtained iterator, then of the second,
and so on. In other words, `it` flattens the iterator of iterators obtained by mapping with
`f`.
-/

namespace Std.Iterators

/-- Internal implementation detail of the `flatMap` combinator -/
@[ext, unbox]
public structure Flatten (α α₂ β : Type w) (m) where
  it₁ : IterM (α := α) m (IterM (α := α₂) m β)
  it₂ : Option (IterM (α := α₂) m β)

/--
Internal iterator combinator that is used to implement all `flatMap` variants
-/
@[always_inline, inline]
def IterM.flattenAfter {α α₂ β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β]
    (it₁ : IterM (α := α) m (IterM (α := α₂) m β)) (it₂ : Option (IterM (α := α₂) m β)) :=
  (toIterM (α := Flatten α α₂ β m) ⟨it₁, it₂⟩ m β : IterM m β)

/--
Let `it₁` and `it₂` be iterators and `f` a monadic function mapping `it₁`'s outputs to iterators
of the same type as `it₂`. Then `it₁.flatMapAfterM f it₂` first goes over `it₂` and then over
`it₁.flatMap f it₂`, emitting all their values.

The main purpose of this combinator is to represent the intermediate state of a `flatMap` iterator
that is currently iterating over one of the inner iterators.

**Marble diagram (without monadic effects):**

```text
it₁                            --b      c    --d -⊥
it₂                      a1-a2⊥
f b                               b1-b2⊥
f c                                      c1-c2⊥
f d                                             ⊥
it.flatMapAfterM f it₂   a1-a2----b1-b2--c1-c2----⊥
```

**Termination properties:**

* `Finite` instance: only if `it₁`, `it₂` and the inner iterators are finite
* `Productive` instance: only if `it₁` is finite and `it₂` and the inner iterators are productive

For certain functions `f`, the resulting iterator will be finite (or productive) even though
no `Finite` (or `Productive`) instance is provided out of the box. For example, if the outer
iterator is productive and the inner
iterators are productive *and provably never empty*, then the resulting iterator is also productive.

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it₁`, `it₂` or an internal
iterator.

For each value emitted by the outer iterator `it₁`, this combinator calls `f`.
-/
@[always_inline, inline]
public def IterM.flatMapAfterM {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β] [Iterator α₂ m γ]
    (f : β → m (IterM (α := α₂) m γ)) (it₁ : IterM (α := α) m β) (it₂ : Option (IterM (α := α₂) m γ)) :=
  ((it₁.mapM f).flattenAfter it₂ : IterM m γ)

/--
Let `it` be an iterator and `f` a monadic function mapping `it`'s outputs to iterators.
Then `it.flatMapM f` is an iterator that goes over `it` and for each output, it applies `f` and
iterates over the resulting iterator. `it.flatMapM f` emits all values obtained from the inner
iterators -- first, all of the first inner iterator, then all of the second one, and so on.

**Marble diagram (without monadic effects):**

```text
it                 ---a      --b      c    --d -⊥
f a                    a1-a2⊥
f b                             b1-b2⊥
f c                                    c1-c2⊥
f d                                           ⊥
it.flatMapM        ----a1-a2----b1-b2--c1-c2----⊥
```

**Termination properties:**

* `Finite` instance: only if `it` and the inner iterators are finite
* `Productive` instance: only if `it` is finite and the inner iterators are productive

For certain functions `f`, the resulting iterator will be finite (or productive) even though
no `Finite` (or `Productive`) instance is provided out of the box. For example, if the outer
iterator is productive and the inner
iterators are productive *and provably never empty*, then the resulting iterator is also productive.

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it` or an internal iterator.

For each value emitted by the outer iterator `it`, this combinator calls `f`.
-/
@[always_inline, inline, expose]
public def IterM.flatMapM {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β] [Iterator α₂ m γ]
    (f : β → m (IterM (α := α₂) m γ)) (it : IterM (α := α) m β) :=
  (it.flatMapAfterM f none : IterM m γ)

/--
Let `it₁` and `it₂` be iterators and `f` a function mapping `it₁`'s outputs to iterators
of the same type as `it₂`. Then `it₁.flatMapAfter f it₂` first goes over `it₂` and then over
`it₁.flatMap f it₂`, emitting all their values.

The main purpose of this combinator is to represent the intermediate state of a `flatMap` iterator
that is currently iterating over one of the inner iterators.

**Marble diagram:**

```text
it₁                            --b      c    --d -⊥
it₂                      a1-a2⊥
f b                               b1-b2⊥
f c                                      c1-c2⊥
f d                                             ⊥
it.flatMapAfter  f it₂   a1-a2----b1-b2--c1-c2----⊥
```

**Termination properties:**

* `Finite` instance: only if `it₁`, `it₂` and the inner iterators are finite
* `Productive` instance: only if `it₁` is finite and `it₂` and the inner iterators are productive

For certain functions `f`, the resulting iterator will be finite (or productive) even though
no `Finite` (or `Productive`) instance is provided out of the box. For example, if the outer
iterator is productive and the inner
iterators are productive *and provably never empty*, then the resulting iterator is also productive.

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it₁`, `it₂` or an internal
iterator.

For each value emitted by the outer iterator `it₁`, this combinator calls `f`.
-/
@[always_inline, inline]
public def IterM.flatMapAfter {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β] [Iterator α₂ m γ]
    (f : β → IterM (α := α₂) m γ) (it₁ : IterM (α := α) m β) (it₂ : Option (IterM (α := α₂) m γ)) :=
  ((it₁.map f).flattenAfter it₂ : IterM m γ)

/--
Let `it` be an iterator and `f` a function mapping `it`'s outputs to iterators.
Then `it.flatMap f` is an iterator that goes over `it` and for each output, it applies `f` and
iterates over the resulting iterator. `it.flatMap f` emits all values obtained from the inner
iterators -- first, all of the first inner iterator, then all of the second one, and so on.

**Marble diagram:**

```text
it                 ---a      --b      c    --d -⊥
f a                    a1-a2⊥
f b                             b1-b2⊥
f c                                    c1-c2⊥
f d                                           ⊥
it.flatMap         ----a1-a2----b1-b2--c1-c2----⊥
```

**Termination properties:**

* `Finite` instance: only if `it` and the inner iterators are finite
* `Productive` instance: only if `it` is finite and the inner iterators are productive

For certain functions `f`, the resulting iterator will be finite (or productive) even though
no `Finite` (or `Productive`) instance is provided out of the box. For example, if the outer
iterator is productive and the inner
iterators are productive *and provably never empty*, then the resulting iterator is also productive.

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it` or an internal iterator.

For each value emitted by the outer iterator `it`, this combinator calls `f`.
-/
@[always_inline, inline, expose]
public def IterM.flatMap {α : Type w} {β : Type w} {α₂ : Type w}
    {γ : Type w} {m : Type w → Type w'} [Monad m] [Iterator α m β] [Iterator α₂ m γ]
    (f : β → IterM (α := α₂) m γ) (it : IterM (α := α) m β) :=
  (it.flatMapAfter f none : IterM m γ)

variable {α α₂ β : Type w} {m : Type w → Type w'}

public instance Flatten.instIterator [Monad m] [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β] :
    Iterator (Flatten α α₂ β m) m β where
  step it :=
    match it with
    | ⟨it₁, none⟩ => do
      match ← it₁.step with
      | .yield it₁' it₂' =>
          return .skip ⟨it₁', some it₂'⟩
      | .skip it₁' =>
          return .skip ⟨it₁', none⟩
      | .done =>
          return .done
    | ⟨it₁, some it₂⟩ => do
      match ← it₂.step with
      | .yield it₂' c =>
          return .yield ⟨it₁, some it₂'⟩ c
      | .skip it₂' =>
          return .skip ⟨it₁, some it₂'⟩
      | .done =>
          return .skip ⟨it₁, none⟩

section Finite

variable {α : Type w} {α₂ : Type w} {β : Type w} {m : Type w → Type w'}

variable (α m β) in
def Rel [Monad m] [MonadAttach m] [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β]
    [Finite α m] [Finite α₂ m] :
    IterM (α := Flatten α α₂ β m) m β → IterM (α := Flatten α α₂ β m) m β → Prop :=
  InvImage
    (Prod.Lex
      (InvImage IterM.TerminationMeasures.Finite.Rel IterM.finitelyManySteps)
      (Option.lt (InvImage IterM.TerminationMeasures.Finite.Rel IterM.finitelyManySteps)))
    (fun it => (it.internalState.it₁, it.internalState.it₂))

theorem Flatten.rel_of_left [Monad m] [MonadAttach m] [Iterator α m (IterM (α := α₂) m β)]
    [Iterator α₂ m β] [Finite α m] [Finite α₂ m] {it it'}
    (h : it'.internalState.it₁.finitelyManySteps.Rel it.internalState.it₁.finitelyManySteps) :
    Rel α β m it' it :=
  Prod.Lex.left _ _ h

theorem Flatten.rel_of_right₁ [Monad m] [MonadAttach m] [Iterator α m (IterM (α := α₂) m β)]
    [Iterator α₂ m β] [Finite α m] [Finite α₂ m] {it₁ it₂ it₂'}
    (h : (InvImage IterM.TerminationMeasures.Finite.Rel IterM.finitelyManySteps) it₂' it₂) :
    Rel α β m ⟨it₁, some it₂'⟩ ⟨it₁, some it₂⟩ := by
  refine Prod.Lex.right _ h

theorem Flatten.rel_of_right₂ [Monad m] [MonadAttach m] [Iterator α m (IterM (α := α₂) m β)]
    [Iterator α₂ m β] [Finite α m] [Finite α₂ m] {it₁ it₂} :
    Rel α β m ⟨it₁, none⟩ ⟨it₁, some it₂⟩ :=
  Prod.Lex.right _ True.intro

def Flatten.instFinitenessRelation
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β]
    [Finite α m] [Finite α₂ m] :
    FinitenessRelation (Flatten α α₂ β m) m where
  rel := Rel α β m
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact InvImage.wf _ WellFoundedRelation.wf
    · exact Option.wellFounded_lt <| InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, hs, h⟩ := h
    simp only [IterM.IsPlausibleStep, Iterator.step] at h
    split at h
    · obtain ⟨step', hs', h⟩ := LawfulMonadAttach.canReturn_bind_imp' h
      cases step', hs' using PlausibleIterStep.casesOn'
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        cases hs
        apply Flatten.rel_of_left
        exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        cases hs
        apply Flatten.rel_of_left
        exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        nomatch hs
    · obtain ⟨step', hs', h⟩ := LawfulMonadAttach.canReturn_bind_imp' h
      cases step', hs' using PlausibleIterStep.casesOn'
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        cases hs
        apply Flatten.rel_of_right₁
        exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        cases hs
        apply Flatten.rel_of_right₁
        exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        cases hs
        apply Flatten.rel_of_right₂

@[no_expose]
public instance Flatten.instFinite
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β]
    [Finite α m] [Finite α₂ m] : Finite (Flatten α α₂ β m) m :=
  .of_finitenessRelation instFinitenessRelation

end Finite

section Productive

variable {α : Type w} {α₂ : Type w} {β : Type w} {m : Type w → Type w'}

variable (α m β) in
def ProductiveRel [Monad m] [MonadAttach m] [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β]
    [Finite α m] [Productive α₂ m] :
    IterM (α := Flatten α α₂ β m) m β → IterM (α := Flatten α α₂ β m) m β → Prop :=
  InvImage
    (Prod.Lex
      (InvImage IterM.TerminationMeasures.Finite.Rel IterM.finitelyManySteps)
      (Option.lt (InvImage IterM.TerminationMeasures.Productive.Rel IterM.finitelyManySkips)))
    (fun it => (it.internalState.it₁, it.internalState.it₂))

theorem Flatten.productiveRel_of_left [Monad m] [MonadAttach m] [Iterator α m (IterM (α := α₂) m β)]
    [Iterator α₂ m β] [Finite α m] [Productive α₂ m] {it it'}
    (h : it'.internalState.it₁.finitelyManySteps.Rel it.internalState.it₁.finitelyManySteps) :
    ProductiveRel α β m it' it :=
  Prod.Lex.left _ _ h

theorem Flatten.productiveRel_of_right₁ [Monad m] [MonadAttach m]
    [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β] [Finite α m] [Productive α₂ m]
    {it₁ it₂ it₂'} (h : (InvImage IterM.TerminationMeasures.Productive.Rel IterM.finitelyManySkips) it₂' it₂) :
    ProductiveRel α β m ⟨it₁, some it₂'⟩ ⟨it₁, some it₂⟩ := by
  refine Prod.Lex.right _ h

theorem Flatten.productiveRel_of_right₂ [Monad m] [MonadAttach m]
    [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β]
    [Finite α m] [Productive α₂ m] {it₁ it₂} :
    ProductiveRel α β m ⟨it₁, none⟩ ⟨it₁, some it₂⟩ :=
  Prod.Lex.right _ True.intro

def Flatten.instProductivenessRelation
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β]
    [Finite α m] [Productive α₂ m] :
    ProductivenessRelation (Flatten α α₂ β m) m where
  rel := ProductiveRel α β m
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact InvImage.wf _ WellFoundedRelation.wf
    · exact Option.wellFounded_lt <| InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp only [IterM.IsPlausibleSkipSuccessorOf, IterM.IsPlausibleStep, Iterator.step] at h
    split at h
    · obtain ⟨step, hs, h⟩ := LawfulMonadAttach.canReturn_bind_imp' h
      cases step, hs using PlausibleIterStep.casesOn'
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        apply Flatten.productiveRel_of_left
        exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        apply Flatten.productiveRel_of_left
        exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›
      · nomatch LawfulMonadAttach.eq_of_canReturn_pure h
    · obtain ⟨step, hs, h⟩ := LawfulMonadAttach.canReturn_bind_imp' h
      cases step, hs using PlausibleIterStep.casesOn'
      · nomatch LawfulMonadAttach.eq_of_canReturn_pure h
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        apply Flatten.productiveRel_of_right₁
        exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›
      · cases LawfulMonadAttach.eq_of_canReturn_pure h
        apply Flatten.productiveRel_of_right₂

@[no_expose]
public instance Flatten.instProductive
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β]
    [Finite α m] [Productive α₂ m] : Productive (Flatten α α₂ β m) m :=
  .of_productivenessRelation instProductivenessRelation

end Productive

public instance Flatten.instIteratorCollect [Monad m] [MonadAttach m] [Monad n]
    [Iterator α m (IterM (α := α₂) m β)]
    [Iterator α₂ m β] : IteratorCollect (Flatten α α₂ β m) m n :=
  .defaultImplementation

public instance Flatten.instIteratorLoop [Monad m] [MonadAttach m] [Monad n] [MonadAttach n]
    [Iterator α m (IterM (α := α₂) m β)] [Iterator α₂ m β] : IteratorLoop (Flatten α α₂ β m) m n :=
  .defaultImplementation

end Std.Iterators
