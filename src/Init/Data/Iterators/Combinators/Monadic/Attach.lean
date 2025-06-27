/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Iterators.Basic
import Init.Data.Iterators.Internal.Termination
import Init.Data.Iterators.Consumers.Collect
import Init.Data.Iterators.Consumers.Loop

namespace Std.Iterators.Types

/--
Internal state of the `attachWith` combinator. Do not depend on its internals.
-/
@[unbox]
structure Attach (α : Type w) (m : Type w → Type w') {β : Type w} [Iterator α m β]
    (P : β → Prop) where
  inner : IterM (α := α) m β
  invariant : ∀ out, inner.IsPlausibleIndirectOutput out → P out

@[always_inline, inline]
def Attach.modifyStep {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {P : β → Prop}
    (it : IterM (α := Attach α m P) m { out : β // P out })
    (step : it.internalState.inner.Step (α := α) (m := m)) :
    IterStep (IterM (α := Attach α m P) m { out : β // P out })
        { out : β // P out } :=
  match step with
  | .yield it' out h =>
    .yield ⟨it', fun out ho => it.internalState.invariant out (.indirect ⟨_, rfl, h⟩ ho)⟩
      ⟨out, it.internalState.invariant out (.direct ⟨_, h⟩)⟩
  | .skip it' h =>
    .skip ⟨it', fun out ho => it.internalState.invariant out (.indirect ⟨_, rfl, h⟩ ho)⟩
  | .done _ => .done

instance Attach.instIterator {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] {P : β → Prop} :
    Iterator (Attach α m P) m { out : β // P out } where
  IsPlausibleStep it step := ∃ step', modifyStep it step' = step
  step it := (fun step => ⟨modifyStep it step, step, rfl⟩) <$> it.internalState.inner.step

def Attach.instFinitenessRelation {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [Finite α m] {P : β → Prop} :
    FinitenessRelation (Attach α m P) m where
  rel := InvImage WellFoundedRelation.rel fun it => it.internalState.inner.finitelyManySteps
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    apply Relation.TransGen.single
    obtain ⟨_, hs, step, h', rfl⟩ := h
    cases step using PlausibleIterStep.casesOn
    · simp only [IterStep.successor, modifyStep, Option.some.injEq] at hs
      simp only [← hs]
      exact ⟨_, rfl, ‹_›⟩
    · simp only [IterStep.successor, modifyStep, Option.some.injEq] at hs
      simp only [← hs]
      exact ⟨_, rfl, ‹_›⟩
    · simp [IterStep.successor, modifyStep, reduceCtorEq] at hs

instance Attach.instFinite {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [Finite α m] {P : β → Prop} : Finite (Attach α m P) m :=
  .of_finitenessRelation instFinitenessRelation

def Attach.instProductivenessRelation {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [Productive α m] {P : β → Prop} :
    ProductivenessRelation (Attach α m P) m where
  rel := InvImage WellFoundedRelation.rel fun it => it.internalState.inner.finitelyManySkips
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    apply Relation.TransGen.single
    simp_wf
    obtain ⟨step, hs⟩ := h
    cases step using PlausibleIterStep.casesOn
    · simp [modifyStep] at hs
    · simp only [modifyStep, IterStep.skip.injEq] at hs
      simp only [← hs]
      assumption
    · simp [modifyStep] at hs

instance Attach.instProductive {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [Productive α m] {P : β → Prop} :
    Productive (Attach α m P) m :=
  .of_productivenessRelation instProductivenessRelation

instance Attach.instIteratorCollect {α β : Type w} {m : Type w → Type w'} [Monad m] [Monad n]
    {P : β → Prop} [Iterator α m β] :
    IteratorCollect (Attach α m P) m n :=
  .defaultImplementation

instance Attach.instIteratorCollectPartial {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Monad n] {P : β → Prop} [Iterator α m β] :
    IteratorCollectPartial (Attach α m P) m n :=
  .defaultImplementation

instance Attach.instIteratorLoop {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Monad n] {P : β → Prop} [Iterator α m β] [MonadLiftT m n] :
    IteratorLoop (Attach α m P) m n :=
  .defaultImplementation

instance Attach.instIteratorLoopPartial {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Monad n] {P : β → Prop} [Iterator α m β] [MonadLiftT m n] :
    IteratorLoopPartial (Attach α m P) m n :=
  .defaultImplementation

instance {α β : Type w} {m : Type w → Type w'} [Monad m]
    {P : β → Prop} [Iterator α m β] [IteratorSize α m] :
    IteratorSize (Attach α m P) m where
  size it := IteratorSize.size it.internalState.inner

instance {α β : Type w} {m : Type w → Type w'} [Monad m]
    {P : β → Prop} [Iterator α m β] [IteratorSizePartial α m] :
    IteratorSizePartial (Attach α m P) m where
  size it := IteratorSizePartial.size it.internalState.inner

end Types

/--
“Attaches” individual proofs to an iterator of values that satisfy a predicate `P`, returning an
iterator with values in the corresponding subtype `{ x // P x }`.

**Termination properties:**

* `Finite` instance: only if the base iterator is finite
* `Productive` instance: only if the base iterator is productive
-/
@[always_inline, inline]
def IterM.attachWith {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] (it : IterM (α := α) m β) (P : β → Prop)
    (h : ∀ out, it.IsPlausibleIndirectOutput out → P out) :
    IterM (α := Types.Attach α m P) m { out : β // P out } :=
  ⟨⟨it, h⟩⟩

end Std.Iterators
