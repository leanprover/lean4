/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Control.Lawful.Basic
import Init.Data.Iterators.Consumers.Monadic.Collect
import Init.Data.Iterators.Consumers.Monadic.Loop
import Init.Data.Iterators.Lemmas.Monadic.Basic
import Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop
import Std.Data.Iterators.Lemmas.Consumers.Monadic.Collect
import Std.Data.Iterators.Lemmas.Equivalence.StepCongr

namespace Std.Iterators

theorem IterM.Equiv.forIn_eq {α₁ α₂ β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Iterator α₁ m β] [Iterator α₂ m β]
    [Finite α₁ m] [Finite α₂ m]
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [IteratorLoop α₁ m n] [LawfulIteratorLoop α₁ m n]
    [IteratorLoop α₂ m n] [LawfulIteratorLoop α₂ m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] {init : γ} {f : β → γ → n (ForInStep γ)}
    {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β} (h : IterM.Equiv ita itb) :
    ForIn.forIn (m := n) ita init f = ForIn.forIn (m := n) itb init f := by
  revert h itb init
  apply ita.inductSteps
  intro ita ihy ihs init itb h
  rw [IterM.forIn_eq_match_step, IterM.forIn_eq_match_step]
  apply h.lift_step_bind_congr
  intro sa sb hs
  simp only [IterStep.bundledQuotient, IterStep.mapIterator_comp, Function.comp_apply] at hs
  cases sa using PlausibleIterStep.casesOn <;> cases sb using PlausibleIterStep.casesOn
  all_goals try exfalso; simp_all; done
  · simp only [IterStep.mapIterator_yield, IterStep.yield.injEq,
      BundledIterM.Equiv.quotMk_eq_iff] at hs
    rcases hs with ⟨hs, rfl⟩
    apply bind_congr
    intro forInStep
    cases forInStep
    · rfl
    · exact ihy ‹_› hs
  · simp only [IterStep.mapIterator_skip, IterStep.skip.injEq,
    BundledIterM.Equiv.quotMk_eq_iff] at hs
    exact ihs ‹_› hs
  · rfl

theorem IterM.Equiv.foldM_eq {α₁ α₂ β γ : Type w} {m : Type w → Type w'}
    {n : Type w → Type w''} [Iterator α₁ m β] [Iterator α₂ m β][Iterator α₁ m β] [Iterator α₂ m β]
    [Finite α₁ m] [Finite α₂ m] [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [IteratorLoop α₁ m n] [LawfulIteratorLoop α₁ m n]
    [IteratorLoop α₂ m n] [LawfulIteratorLoop α₂ m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] {init : γ} {f : γ → β → n γ}
    {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β} (h : IterM.Equiv ita itb) :
    ita.foldM (init := init) f = itb.foldM (init := init) f := by
  simp [IterM.foldM_eq_forIn, h.forIn_eq]

theorem IterM.Equiv.fold_eq {α₁ α₂ β γ : Type w} {m : Type w → Type w'}
    [Iterator α₁ m β] [Iterator α₂ m β][Iterator α₁ m β] [Iterator α₂ m β]
    [Finite α₁ m] [Finite α₂ m] [Monad m] [LawfulMonad m]
    [IteratorLoop α₁ m m] [LawfulIteratorLoop α₁ m m]
    [IteratorLoop α₂ m m] [LawfulIteratorLoop α₂ m m]
    {init : γ} {f : γ → β → γ}
    {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β} (h : IterM.Equiv ita itb) :
    ita.fold (init := init) f = itb.fold (init := init) f := by
  simp [IterM.fold_eq_foldM, h.foldM_eq]

theorem IterM.Equiv.drain_eq {α₁ α₂ β : Type w} {m : Type w → Type w'}
    [Iterator α₁ m β] [Iterator α₂ m β][Iterator α₁ m β] [Iterator α₂ m β]
    [Finite α₁ m] [Finite α₂ m] [Monad m] [LawfulMonad m]
    [IteratorLoop α₁ m m] [LawfulIteratorLoop α₁ m m]
    [IteratorLoop α₂ m m] [LawfulIteratorLoop α₂ m m]
    {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β} (h : IterM.Equiv ita itb) :
    ita.drain = itb.drain := by
  simp [IterM.drain_eq_fold, h.fold_eq]

end Std.Iterators
