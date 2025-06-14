/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Data.Array.Lemmas
import Init.Data.Iterators.Consumers.Monadic.Collect
import Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect
import Init.Data.Iterators.Lemmas.Monadic.Basic
import Std.Data.Iterators.Lemmas.Equivalence.StepCongr

namespace Std.Iterators

theorem IterM.Equiv.toListRev_eq [Monad m] [LawfulMonad m]
    [Iterator α₁ m β] [Iterator α₂ m β] [Finite α₁ m] [Finite α₂ m]
    {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β} (h : IterM.Equiv ita itb) :
    ita.toListRev = itb.toListRev := by
  induction ita using IterM.inductSteps generalizing itb with | step ita ihy ihs =>
  rw [IterM.toListRev_eq_match_step, IterM.toListRev_eq_match_step]
  apply h.lift_step_bind_congr
  intro s₁ s₂ h
  simp only [IterStep.bundledQuotient] at h
  cases s₁ using PlausibleIterStep.casesOn <;> cases s₂ using PlausibleIterStep.casesOn
  all_goals try exfalso; simp_all; done
  · simp only [IterStep.mapIterator_yield, Function.comp_apply, IterStep.yield.injEq] at h
    simp_all only [bind_pure_comp, List.append_cancel_right_eq, implies_true,
      map_inj_right_of_nonempty]
    apply ihy ‹_›
    exact BundledIterM.Equiv.exact _ _ h.1
  · simp only [IterStep.mapIterator_skip, Function.comp_apply, IterStep.skip.injEq] at ⊢ h
    apply ihs ‹_›
    exact BundledIterM.Equiv.exact _ _ h
  · simp

theorem IterM.Equiv.toList_eq {α₁ α₂ : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α₁ m β] [Iterator α₂ m β] [Finite α₁ m] [Finite α₂ m]
    [IteratorCollect α₁ m m] [LawfulIteratorCollect α₁ m m]
    [IteratorCollect α₂ m m] [LawfulIteratorCollect α₂ m m]
    {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β} (h : IterM.Equiv ita itb) :
    ita.toList = itb.toList := by
  simp only [← IterM.reverse_toListRev, toListRev_eq h]

theorem IterM.Equiv.toArray_eq [Monad m] [LawfulMonad m]
    [Iterator α₁ m β] [Iterator α₂ m β] [Finite α₁ m] [Finite α₂ m]
    [IteratorCollect α₁ m m] [LawfulIteratorCollect α₁ m m]
    [IteratorCollect α₂ m m] [LawfulIteratorCollect α₂ m m]
    {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β} (h : IterM.Equiv ita itb) :
    ita.toArray = itb.toArray := by
  simp only [← IterM.toArray_toList, toList_eq h]

end Std.Iterators
