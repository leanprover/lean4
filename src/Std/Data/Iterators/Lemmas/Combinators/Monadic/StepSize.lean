/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Std.Data.Iterators.Combinators.Monadic.StepSize
import Init.Data.Iterators.Lemmas.Consumers.Monadic.Access
import all Init.Data.Iterators.Consumers.Monadic.Access
import Init.Classical

public section
open Std Std.Iterators Std.Iterators.Types

namespace Std.IterM

instance instLawfulDeterministicIteratorStepSizeIterator
    [Iterator α Id β] [LawfulDeterministicIterator α Id] [IteratorAccess α Id] :
    LawfulDeterministicIterator (Types.StepSizeIterator α Id β) Id where
  isPlausibleStep_eq_eq it := by
    refine ⟨it.step.run.inflate.val, ?_⟩
    have hp := it.step.run.inflate.property
    ext step
    constructor
    · intro ⟨h₁, h₂⟩
      obtain ⟨hp₁, hp₂⟩ := hp
      simp only [IterStep.mapIterator] at h₁ hp₁
      have heq := h₁.unique hp₁
      generalize it.step.run.inflate.val = cstep at heq hp₁ hp₂ ⊢
      cases step with
      | skip _ => exact IterM.not_isPlausibleNthOutputStep_skip.elim (by simpa using h₁)
      | done =>
        cases cstep with
        | done => simp
        | yield _ _ => simp at heq
        | skip _ => exact IterM.not_isPlausibleNthOutputStep_skip.elim (by simpa using hp₁)
      | yield it₁ out₁ =>
        cases cstep with
        | done => simp at heq
        | skip _ => exact IterM.not_isPlausibleNthOutputStep_skip.elim (by simpa using hp₁)
        | yield it₂ out₂ =>
          rcases it₁ with ⟨⟨_, _, _⟩⟩
          rcases it₂ with ⟨⟨_, _, _⟩⟩
          simp_all
    · simpa +contextual using fun _ => hp

theorem nextAtIdxSlow?_stepSize_aux [Iterator α Id β] [Productive α Id] [LawfulDeterministicIterator α Id]
    [IteratorAccess α Id] {it : IterM (α := α) Id β} {n : Nat} :
    (IterM.Intermediate.stepSize it i n).nextAtIdxSlow? 0 = (do
      match (← it.nextAtIdxSlow? i) with
      | .yield it' out h =>
        return .yield (IterM.Intermediate.stepSize it' (n - 1) n) out (by
          refine .zero_yield ?_
          simpa [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, IterM.Intermediate.stepSize,
            IterM.Intermediate.stepSize, StepSizeIterator.instIterator]) -- TODO: remove `inst...` argument as soon as possible
      | .skip it' h => return IterM.not_isPlausibleNthOutputStep_skip.elim h
      | .done h =>
        return .done (by
          refine .done ?_
          simpa [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, Intermediate.stepSize,
            IterM.Intermediate.stepSize, StepSizeIterator.instIterator])) := by -- TODO: remove `inst...` argument as soon as possible
  induction it, i using IterM.atIdxSlow?.induct_unfolding
  rw [IterM.nextAtIdxSlow?_eq_match]
  simp only [IterM.Intermediate.stepSize, IterM.step_eq, IterM.internalState_mk,
    IterM.nextAtIdx?_eq_nextAtIdxSlow?, bind_pure_comp, bind_map_left, Shrink.inflate_deflate]
  apply bind_congr; intro step
  cases step using PlausibleIterStep.casesOn
  · simp
  · exact IterM.not_isPlausibleNthOutputStep_skip.elim ‹_›
  · simp

end Std.IterM
