/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Internal.Termination
public import Init.Data.Iterators.Consumers.Loop
import Init.Control.Lawful.MonadAttach.Lemmas

public section

namespace Std.Iterators.Types

/--
Internal state of the `attachWith` combinator. Do not depend on its internals.
-/
@[unbox]
structure Attach (α : Type w) (m : Type w → Type w') {β : Type w} [MonadAttach m] [Iterator α m β]
    (P : β → Prop) where
  inner : IterM (α := α) m β
  invariant : ∀ out, inner.IsPlausibleIndirectOutput out → P out

instance Attach.instIterator {α β : Type w} {m : Type w → Type w'} [Monad m] [MonadAttach m]
    [Iterator α m β] {P : β → Prop} :
    Iterator (Attach α m P) m { out : β // P out } where
  step it := (fun ⟨step, hs⟩ =>
    match step with
    | .yield it' out =>
      .yield ⟨it', fun out ho => it.internalState.invariant out (.indirect ⟨_, rfl, hs⟩ ho)⟩
        ⟨out, it.internalState.invariant out (.direct ⟨_, hs⟩)⟩
    | .skip it' =>
      .skip ⟨it', fun out ho => it.internalState.invariant out (.indirect ⟨_, rfl, hs⟩ ho)⟩
    | .done => .done) <$> MonadAttach.attach it.internalState.inner.step

def Attach.instFinitenessRelation {α β : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Iterator α m β] [Finite α m] {P : β → Prop} :
    FinitenessRelation (Attach α m P) m where
  rel := InvImage WellFoundedRelation.rel fun it => it.internalState.inner.finitelyManySteps
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨_, hs, h⟩ := h
    obtain ⟨step, h', rfl⟩ := LawfulMonadAttach.canReturn_map_imp' h
    cases step using PlausibleIterStep.casesOn
    · simp only [IterStep.successor, Option.some.injEq] at hs
      simp only [← hs]
      exact IterM.TerminationMeasures.Finite.rel_of_yield ‹_›
    · simp only [IterStep.successor, Option.some.injEq] at hs
      simp only [← hs]
      exact IterM.TerminationMeasures.Finite.rel_of_skip ‹_›
    · simp [IterStep.successor, reduceCtorEq] at hs

instance Attach.instFinite {α β : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Iterator α m β] [Finite α m] {P : β → Prop} : Finite (Attach α m P) m :=
  .of_finitenessRelation instFinitenessRelation

def Attach.instProductivenessRelation {α β : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Iterator α m β] [Productive α m] {P : β → Prop} :
    ProductivenessRelation (Attach α m P) m where
  rel := InvImage WellFoundedRelation.rel fun it => it.internalState.inner.finitelyManySkips
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    obtain ⟨step, h', h⟩ := LawfulMonadAttach.canReturn_map_imp' h
    cases step using PlausibleIterStep.casesOn
    · cases h
    · cases h
      exact IterM.TerminationMeasures.Productive.rel_of_skip ‹_›
    · cases h

instance Attach.instProductive {α β : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [LawfulMonad m] [LawfulMonadAttach m]
    [Iterator α m β] [Productive α m] {P : β → Prop} :
    Productive (Attach α m P) m :=
  .of_productivenessRelation instProductivenessRelation

instance Attach.instIteratorCollect {α β : Type w} {m : Type w → Type w'}
    [Monad m] [MonadAttach m] [Monad n]
    {P : β → Prop} [Iterator α m β] :
    IteratorCollect (Attach α m P) m n :=
  .defaultImplementation

instance Attach.instIteratorLoop {α β : Type w} {m : Type w → Type w'} [Monad m] [MonadAttach m]
    {n : Type x → Type x'} [Monad n] [MonadAttach n] {P : β → Prop} [Iterator α m β] :
    IteratorLoop (Attach α m P) m n :=
  .defaultImplementation

end Types

/--
“Attaches” individual proofs to an iterator of values that satisfy a predicate `P`, returning an
iterator with values in the corresponding subtype `{ x // P x }`.

**Termination properties:**

* `Finite` instance: only if the base iterator is finite
* `Productive` instance: only if the base iterator is productive
-/
@[always_inline, inline, expose]
def IterM.attachWith {α β : Type w} {m : Type w → Type w'} [Monad m] [MonadAttach m]
    [Iterator α m β] (it : IterM (α := α) m β) (P : β → Prop)
    (h : ∀ out, it.IsPlausibleIndirectOutput out → P out) :
    IterM (α := Types.Attach α m P) m { out : β // P out } :=
  ⟨⟨it, h⟩⟩

end Std.Iterators
