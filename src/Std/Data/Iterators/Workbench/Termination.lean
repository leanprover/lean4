/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Basic

namespace Std.Iterators

variable (α m) in
class FinitenessRelation [Iterator α m β] where
  rel : (IterM (α := α) m β) → (IterM (α := α) m β) → Prop
  wf : WellFounded rel
  subrelation : ∀ {it it'}, it'.plausible_successor_of it → rel it' it

instance [Iterator α m β] [FinitenessRelation α m] : Finite α m where
  wf := by
    refine Subrelation.wf (r := FinitenessRelation.rel) ?_ ?_
    · intro x y h
      apply FinitenessRelation.subrelation
      exact h
    · apply InvImage.wf
      exact FinitenessRelation.wf

theorem IterM.plausible_successor_of_yield
    {α : Type w} {m : Type w → Type w'} {β : Type w} [Iterator α m β]
    {it' it : IterM (α := α) m β} {out : β} (h : it.plausible_step (.yield it' out)) :
    it'.plausible_successor_of it :=
  ⟨_, rfl, h⟩

theorem IterM.plausible_successor_of_skip
    {α m β} [Iterator α m β] {it it' : IterM (α := α) m β}
    (h : it.plausible_step (.skip it')) :
    it'.plausible_successor_of it :=
  ⟨_, rfl, h⟩

variable (α m) in
class ProductivenessRelation [Iterator α m β] where
  rel : (IterM (α := α) m β) → (IterM (α := α) m β) → Prop
  wf : WellFounded rel
  subrelation : ∀ {it it'}, it'.plausible_skip_successor_of it → rel it' it

instance [Iterator α m β] [ProductivenessRelation α m] : Productive α m where
  wf := by
    refine Subrelation.wf (r := ProductivenessRelation.rel) ?_ ?_
    · intro x y h
      apply ProductivenessRelation.subrelation
      exact h
    · apply InvImage.wf
      exact ProductivenessRelation.wf

instance [Iterator α m β] [Finite α m] : Productive α m where
  wf := by
    apply Subrelation.wf (r := IterM.plausible_successor_of)
    · intro it' it h
      exact IterM.plausible_successor_of_skip h
    · exact Finite.wf

end Std.Iterators
