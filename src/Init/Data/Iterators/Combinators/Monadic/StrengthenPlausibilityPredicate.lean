/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Internal.Termination
public import Init.Data.Iterators.Consumers.Loop
public import Init.Control.MonadAttach

namespace Std.Iterators.Types

@[unbox]
public structure StrengthenPlausibilityPredicate (α : Type w) where
  inner : α

namespace StrengthenPlausibilityPredicate

public instance instIterator {α β : Type w} {m : Type w → Type w'} [Monad m] [MonadAttach m]
    [Iterator α m β] : Iterator (StrengthenPlausibilityPredicate α) m β where
  IsPlausibleStep it step :=
    ∃ h, MonadAttach.CanReturn (toIterM it.internalState.inner m β).step
        (.deflate ⟨step.mapIterator fun it' => ⟨it'.internalState.inner⟩, h⟩)
  step it := do
    (fun ⟨step, h⟩ => .deflate ⟨
          step.inflate.val.mapIterator (fun it' => ⟨⟨it'.internalState⟩⟩),
            by simpa [Function.comp_def] using step.inflate.property,
            by simpa [Function.comp_def, Subtype.eta] using h⟩) <$>
      MonadAttach.attach (toIterM it.internalState.inner m β).step

def instFinitenessRelation {α β : Type w} {m : Type w → Type w'} [Monad m] [MonadAttach m]
    [Iterator α m β] [Finite α m] : FinitenessRelation (StrengthenPlausibilityPredicate α) m where
  rel := InvImage WellFoundedRelation.rel (toIterM ·.internalState.inner m β |>.finitelyManySteps)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    apply Relation.TransGen.single
    obtain ⟨step, hs, h, _⟩ := h
    cases step
    · cases hs
      exact ⟨_, rfl, ‹_›⟩
    · cases hs
      exact ⟨_, rfl, ‹_›⟩
    · nomatch hs

@[no_expose]
public instance instFinite {α β : Type w} {m : Type w → Type w'} [Monad m] [MonadAttach m]
    [Iterator α m β] [Finite α m] : Finite (StrengthenPlausibilityPredicate α) m :=
  .of_finitenessRelation instFinitenessRelation

def instProductivenessRelation {α β : Type w} {m : Type w → Type w'} [Monad m] [MonadAttach m]
    [Iterator α m β] [Productive α m] : ProductivenessRelation (StrengthenPlausibilityPredicate α) m where
  rel := InvImage WellFoundedRelation.rel (toIterM ·.internalState.inner m β |>.finitelyManySkips)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation h := Relation.TransGen.single h.1

@[no_expose]
public instance instProductive {α β : Type w} {m : Type w → Type w'} [Monad m] [MonadAttach m]
    [Iterator α m β] [Productive α m] : Productive (StrengthenPlausibilityPredicate α) m :=
  .of_productivenessRelation instProductivenessRelation

public instance instIteratorCollect {α β : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [MonadAttach m] [Monad n] [Iterator α m β] [IteratorCollect α m n] :
    IteratorCollect (StrengthenPlausibilityPredicate α) m n where
  toArrayMapped lift {_ f} it :=
    IteratorCollect.toArrayMapped lift f (toIterM it.internalState.inner m β)

public instance instLawfulIteratorCollect {α β : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [MonadAttach m] [Monad n] [Iterator α m β] [IteratorCollect α m n]
    [LawfulIteratorCollect α m n] :
    LawfulIteratorCollect (StrengthenPlausibilityPredicate α) m n where
  lawful_toArrayMapped γ lift _ := by
    ext
    simp [instIteratorCollect]
    rw [LawfulIteratorCollect.toArrayMapped_eq]

public instance instIteratorLoop {α β : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [MonadAttach m] [Monad n] [Iterator α m β] :
    IteratorLoop (StrengthenPlausibilityPredicate α) m n :=
  .defaultImplementation

end StrengthenPlausibilityPredicate

end Std.Iterators.Types
