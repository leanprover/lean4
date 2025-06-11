/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Iterators.Basic

/-!
This is an internal module used by iterator implementations.
-/

namespace Std.Iterators

/--
Internal implementation detail of the iterator library.
The purpose of this class is that it implies a `Finite` instance but
it is more convenient to implement.
-/
structure FinitenessRelation (α : Type w) (m : Type w → Type w') {β : Type w}
    [Iterator α m β] where
  rel : (IterM (α := α) m β) → (IterM (α := α) m β) → Prop
  wf : WellFounded rel
  subrelation : ∀ {it it'}, it'.IsPlausibleSuccessorOf it → rel it' it

theorem Finite.of_finitenessRelation
    {α : Type w} {m : Type w → Type w'} {β : Type w}
    [Iterator α m β] (r : FinitenessRelation α m) : Finite α m where
  wf := by
    refine Subrelation.wf (r := r.rel) ?_ ?_
    · intro x y h
      apply FinitenessRelation.subrelation
      exact h
    · apply InvImage.wf
      exact r.wf

/--
Internal implementation detail of the iterator library.
The purpose of this class is that it implies a `Productive` instance but
it is more convenient to implement.
-/
structure ProductivenessRelation (α : Type w) (m : Type w → Type w') {β : Type w}
    [Iterator α m β] where
  rel : (IterM (α := α) m β) → (IterM (α := α) m β) → Prop
  wf : WellFounded rel
  subrelation : ∀ {it it'}, it'.IsPlausibleSkipSuccessorOf it → rel it' it

theorem Productive.of_productivenessRelation
    {α : Type w} {m : Type w → Type w'} {β : Type w}
    [Iterator α m β] (r : ProductivenessRelation α m) : Productive α m where
  wf := by
    refine Subrelation.wf (r := r.rel) ?_ ?_
    · intro x y h
      apply ProductivenessRelation.subrelation
      exact h
    · apply InvImage.wf
      exact r.wf

end Std.Iterators
