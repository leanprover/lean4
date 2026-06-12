/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers.Monadic.Loop
public import Init.Classical
import Init.Data.Option.Lemmas
import Init.ByCases
import Init.Omega

public section

/-!
This module provides the iterator combinator `IterM.append`.
-/

namespace Std

variable {α : Type w} {m : Type w → Type w'} {β : Type w}

/--
The internal state of the `IterM.append` iterator combinator.
-/
inductive Iterators.Types.Append (α₁ α₂ : Type w) (m : Type w → Type w') (β : Type w) where
  | fst : IterM (α := α₁) m β → IterM (α := α₂) m β → Append α₁ α₂ m β
  | snd : IterM (α := α₂) m β → Append α₁ α₂ m β

open Std.Iterators Std.Iterators.Types

/--
Given two iterators `it₁` and `it₂`, `it₁.append it₂` is an iterator that first outputs all values
of `it₁` in order and then all values of `it₂` in order.

**Marble diagram:**

```text
it₁                 ---a----b---c--⊥
it₂                                 --d--e--⊥
it₁.append it₂      ---a----b---c-----d--e--⊥
```

**Termination properties:**

* `Finite` instance: only if `it₁` and `it₂` are finite
* `Productive` instance: only if `it₁` and `it₂` are productive

Note: If `it₁` is not finite, then `it₁.append it₂` can be productive while `it₂` is not.
The standard library does not provide a `Productive` instance for this case.

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it₁` and `it₂`.
-/
@[inline, expose]
def IterM.append [Iterator α₁ m β] [Iterator α₂ m β]
    (it₁ : IterM (α := α₁) m β) (it₂ : IterM (α := α₂) m β) :=
  (⟨Iterators.Types.Append.fst it₁ it₂⟩ : IterM m β)

/--
This combinator is only useful for advanced use cases.

Given an iterator `it₂`, `IterM.Intermediate.appendSnd α₁ it₂` returns an iterator that behaves
exactly like `it₂` but has the same type as `it₁.append it₂` (after `it₁` has been exhausted).
This is useful for constructing intermediate states of the append iterator.

**Marble diagram:**

```text
it₂                                  --a--b--⊥
IterM.Intermediate.appendSnd α₁ it₂  --a--b--⊥
```

**Termination properties:**

* `Finite` instance: only if `it₂` and iterators of type `α₁` are finite
* `Productive` instance: only if `it₂` and iterators of type `α₁` are productive

Note: If iterators of type `α₁` are not finite, then `appendSnd α₁ it₂` can be productive
while `it₂` is not. The standard library does not provide a `Productive` instance for this case.

**Performance:**

This combinator incurs an additional O(1) cost with each output of `it₂`.
-/
@[inline, expose]
def IterM.Intermediate.appendSnd [Iterator α₂ m β] (α₁ : Type w) (it₂ : IterM (α := α₂) m β) :=
  (⟨Iterators.Types.Append.snd (α₁ := α₁) it₂⟩ : IterM m β)

namespace Iterators.Types

inductive Append.PlausibleStep [Iterator α₁ m β] [Iterator α₂ m β] :
    IterM (α := Append α₁ α₂ m β) m β → IterStep (IterM (α := Append α₁ α₂ m β) m β) β → Prop where
  | fstYield {it₁ : IterM (α := α₁) m β}  {it₂ : IterM (α := α₂) m β} :
    it₁.IsPlausibleStep (.yield it₁' out) → PlausibleStep (it₁.append it₂) (.yield (it₁'.append it₂) out)
  | fstSkip {it₁ : IterM (α := α₁) m β} {it₂ : IterM (α := α₂) m β} :
    it₁.IsPlausibleStep (.skip it₁') → PlausibleStep (it₁.append it₂) (.skip (it₁'.append it₂))
  | fstDone {it₁ : IterM (α := α₁) m β} {it₂ : IterM (α := α₂) m β} :
    it₁.IsPlausibleStep .done → PlausibleStep (it₁.append it₂) (.skip (IterM.Intermediate.appendSnd α₁ it₂))
  | sndYield {it₂ : IterM (α := α₂) m β} :
    it₂.IsPlausibleStep (.yield it₂' out) →
      PlausibleStep (IterM.Intermediate.appendSnd α₁ it₂) (.yield (IterM.Intermediate.appendSnd α₁ it₂') out)
  | sndSkip {it₂ : IterM (α := α₂) m β} :
    it₂.IsPlausibleStep (.skip it₂') →
      PlausibleStep (IterM.Intermediate.appendSnd α₁ it₂) (.skip (IterM.Intermediate.appendSnd α₁ it₂'))
  | sndDone {it₂ : IterM (α := α₂) m β} :
    it₂.IsPlausibleStep .done → PlausibleStep (IterM.Intermediate.appendSnd α₁ it₂) .done

@[inline]
instance Append.instIterator [Monad m] [Iterator α₁ m β] [Iterator α₂ m β] :
    Iterator (Append α₁ α₂ m β) m β where
  IsPlausibleStep := Append.PlausibleStep
  step
    | ⟨.fst it₁ it₂⟩ => do
      match (← it₁.step).inflate with
      | .yield it₁' out h => return .deflate <| .yield (it₁'.append it₂) out (.fstYield h)
      | .skip it₁' h => return .deflate <| .skip (it₁'.append it₂) (.fstSkip h)
      | .done h => return .deflate <| .skip (IterM.Intermediate.appendSnd α₁ it₂) (.fstDone h)
    | ⟨.snd it₂⟩ => do
      match (← it₂.step).inflate with
      | .yield it₂' out h => return .deflate <| .yield (IterM.Intermediate.appendSnd α₁ it₂') out (.sndYield h)
      | .skip it₂' h => return .deflate <| .skip (IterM.Intermediate.appendSnd α₁ it₂') (.sndSkip h)
      | .done h => return .deflate <| .done (.sndDone h)

instance Append.instIteratorLoop {n : Type x → Type x'} [Monad m] [Monad n]
    [Iterator α₁ m β] [Iterator α₂ m β] :
    IteratorLoop (Append α₁ α₂ m β) m n :=
  .defaultImplementation

section Finite

variable {α₁ : Type w} {α₂ : Type w} {m : Type w → Type w'} {β : Type w}

variable (α₁ α₂ m β) in
def Append.Rel [Monad m] [Iterator α₁ m β] [Iterator α₂ m β] [Finite α₁ m] [Finite α₂ m] :
    IterM (α := Append α₁ α₂ m β) m β → IterM (α := Append α₁ α₂ m β) m β → Prop :=
  InvImage
    (Prod.Lex
      (Option.lt (InvImage IterM.TerminationMeasures.Finite.Rel IterM.finitelyManySteps))
      (InvImage IterM.TerminationMeasures.Finite.Rel IterM.finitelyManySteps))
    (fun it => match it.internalState with
      | .fst it₁ it₂ => (some it₁, it₂)
      | .snd it₂ => (none, it₂))

theorem Append.rel_of_fst [Monad m] [Iterator α₁ m β] [Iterator α₂ m β]
    [Finite α₁ m] [Finite α₂ m] {it₁ it₁' : IterM (α := α₁) m β} {it₂ : IterM (α := α₂) m β}
    (h : it₁'.finitelyManySteps.Rel it₁.finitelyManySteps) :
    Append.Rel α₁ α₂ m β (it₁'.append it₂) (it₁.append it₂) := by
  exact Prod.Lex.left _ _ h

theorem Append.rel_fstDone [Monad m] [Iterator α₁ m β] [Iterator α₂ m β]
    [Finite α₁ m] [Finite α₂ m] {it₁ : IterM (α := α₁) m β} {it₂ : IterM (α := α₂) m β} :
    Append.Rel α₁ α₂ m β (IterM.Intermediate.appendSnd α₁ it₂) (it₁.append it₂) := by
  exact Prod.Lex.left _ _ trivial

theorem Append.rel_of_snd [Monad m] [Iterator α₁ m β] [Iterator α₂ m β]
    [Finite α₁ m] [Finite α₂ m] {it₂ it₂' : IterM (α := α₂) m β}
    (h : it₂'.finitelyManySteps.Rel it₂.finitelyManySteps) :
    Append.Rel α₁ α₂ m β (IterM.Intermediate.appendSnd α₁ it₂') (IterM.Intermediate.appendSnd α₁ it₂) := by
  exact Prod.Lex.right _ h

def Append.instFinitenessRelation [Monad m] [Iterator α₁ m β] [Iterator α₂ m β]
    [Finite α₁ m] [Finite α₂ m] :
    FinitenessRelation (Append α₁ α₂ m β) m where
  Rel := Append.Rel α₁ α₂ m β
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact Option.wellFounded_lt <| InvImage.wf _ WellFoundedRelation.wf
    · exact InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, h, h'⟩ := h
    cases h' <;> cases h
    case fstYield =>
      apply Append.rel_of_fst
      exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
    case fstSkip =>
      apply Append.rel_of_fst
      exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›
    case fstDone =>
      exact Append.rel_fstDone
    case sndYield =>
      apply Append.rel_of_snd
      exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
    case sndSkip =>
      apply Append.rel_of_snd
      exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›

instance Append.instFinite [Monad m] [Iterator α₁ m β] [Iterator α₂ m β]
    [Finite α₁ m] [Finite α₂ m] : Finite (Append α₁ α₂ m β) m :=
  .of_finitenessRelation instFinitenessRelation

end Finite

section Productive

variable {α₁ : Type w} {α₂ : Type w} {m : Type w → Type w'} {β : Type w}

variable (α₁ α₂ m β) in
def Append.ProductiveRel [Monad m] [Iterator α₁ m β] [Iterator α₂ m β]
    [Productive α₁ m] [Productive α₂ m] :
    IterM (α := Append α₁ α₂ m β) m β → IterM (α := Append α₁ α₂ m β) m β → Prop :=
  InvImage
    (Prod.Lex
      (Option.lt (InvImage IterM.TerminationMeasures.Productive.Rel IterM.finitelyManySkips))
      (InvImage IterM.TerminationMeasures.Productive.Rel IterM.finitelyManySkips))
    (fun it => match it.internalState with
      | .fst it₁ it₂ => (some it₁, it₂)
      | .snd it₂ => (none, it₂))

theorem Append.productiveRel_of_fst [Monad m] [Iterator α₁ m β] [Iterator α₂ m β]
    [Productive α₁ m] [Productive α₂ m] {it₁ it₁' : IterM (α := α₁) m β}
    {it₂ : IterM (α := α₂) m β}
    (h : it₁'.finitelyManySkips.Rel it₁.finitelyManySkips) :
    Append.ProductiveRel α₁ α₂ m β (it₁'.append it₂) (it₁.append it₂) := by
  exact Prod.Lex.left _ _ h

theorem Append.productiveRel_fstDone [Monad m] [Iterator α₁ m β] [Iterator α₂ m β]
    [Productive α₁ m] [Productive α₂ m] {it₁ : IterM (α := α₁) m β}
    {it₂ : IterM (α := α₂) m β} :
    Append.ProductiveRel α₁ α₂ m β (IterM.Intermediate.appendSnd α₁ it₂) (it₁.append it₂) := by
  exact Prod.Lex.left _ _ trivial

theorem Append.productiveRel_of_snd [Monad m] [Iterator α₁ m β] [Iterator α₂ m β]
    [Productive α₁ m] [Productive α₂ m] {it₂ it₂' : IterM (α := α₂) m β}
    (h : it₂'.finitelyManySkips.Rel it₂.finitelyManySkips) :
    Append.ProductiveRel α₁ α₂ m β
      (IterM.Intermediate.appendSnd α₁ it₂') (IterM.Intermediate.appendSnd α₁ it₂) := by
  exact Prod.Lex.right _ h

private def Append.instProductivenessRelation [Monad m] [Iterator α₁ m β] [Iterator α₂ m β]
    [Productive α₁ m] [Productive α₂ m] :
    ProductivenessRelation (Append α₁ α₂ m β) m where
  Rel := Append.ProductiveRel α₁ α₂ m β
  wf := by
    apply InvImage.wf
    refine ⟨fun (a, b) => Prod.lexAccessible (WellFounded.apply ?_ a) (WellFounded.apply ?_) b⟩
    · exact Option.wellFounded_lt <| InvImage.wf _ WellFoundedRelation.wf
    · exact InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    cases h
    case fstSkip =>
      apply Append.productiveRel_of_fst
      exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›
    case fstDone =>
      exact Append.productiveRel_fstDone
    case sndSkip =>
      apply Append.productiveRel_of_snd
      exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›

instance Append.instProductive [Monad m] [Iterator α₁ m β] [Iterator α₂ m β]
    [Productive α₁ m] [Productive α₂ m] : Productive (Append α₁ α₂ m β) m :=
  .of_productivenessRelation instProductivenessRelation

end Productive

end Std.Iterators.Types
