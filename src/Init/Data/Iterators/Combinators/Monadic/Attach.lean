/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers.Loop

public section

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
def Attach.Monadic.modifyStep {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
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
  IsPlausibleStep it step := ∃ step', Monadic.modifyStep it step' = step
  step it := (fun step => .deflate ⟨Monadic.modifyStep it step.inflate, step.inflate, rfl⟩) <$>
      it.internalState.inner.step

def Attach.instFinitenessRelation {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [Finite α m] {P : β → Prop} :
    FinitenessRelation (Attach α m P) m where
  Rel := InvImage WellFoundedRelation.rel fun it => it.internalState.inner.finitelyManySteps
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    apply Relation.TransGen.single
    obtain ⟨_, hs, step, h', rfl⟩ := h
    cases step using PlausibleIterStep.casesOn
    · simp only [IterStep.successor, Monadic.modifyStep, Option.some.injEq] at hs
      simp only [← hs]
      exact ⟨_, rfl, ‹_›⟩
    · simp only [IterStep.successor, Monadic.modifyStep, Option.some.injEq] at hs
      simp only [← hs]
      exact ⟨_, rfl, ‹_›⟩
    · simp [IterStep.successor, Monadic.modifyStep, reduceCtorEq] at hs

instance Attach.instFinite {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [Finite α m] {P : β → Prop} : Finite (Attach α m P) m :=
  .of_finitenessRelation instFinitenessRelation

def Attach.instProductivenessRelation {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [Productive α m] {P : β → Prop} :
    ProductivenessRelation (Attach α m P) m where
  Rel := InvImage WellFoundedRelation.rel fun it => it.internalState.inner.finitelyManySkips
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    apply Relation.TransGen.single
    simp_wf
    obtain ⟨step, hs⟩ := h
    cases step using PlausibleIterStep.casesOn
    · simp [Monadic.modifyStep] at hs
    · simp only [Monadic.modifyStep, IterStep.skip.injEq] at hs
      simp only [← hs]
      assumption
    · simp [Monadic.modifyStep] at hs

instance Attach.instProductive {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] [Productive α m] {P : β → Prop} :
    Productive (Attach α m P) m :=
  .of_productivenessRelation instProductivenessRelation

instance Attach.instIteratorLoop {α β : Type w} {m : Type w → Type w'} [Monad m]
    {n : Type x → Type x'} [Monad n] {P : β → Prop} [Iterator α m β] :
    IteratorLoop (Attach α m P) m n :=
  .defaultImplementation

end Iterators.Types

/--
“Attaches” individual proofs to an iterator of values that satisfy a predicate `P`, returning an
iterator with values in the corresponding subtype `{ x // P x }`.

**Termination properties:**

* `Finite` instance: only if the base iterator is finite
* `Productive` instance: only if the base iterator is productive
-/
@[always_inline, inline, expose]
def IterM.attachWith {α β : Type w} {m : Type w → Type w'} [Monad m]
    [Iterator α m β] (it : IterM (α := α) m β) (P : β → Prop)
    (h : ∀ out, it.IsPlausibleIndirectOutput out → P out) :
    IterM (α := Iterators.Types.Attach α m P) m { out : β // P out } :=
  ⟨⟨it, h⟩⟩

end Std
