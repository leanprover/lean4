/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap
public import Std.Data.Iterators.Lemmas.Equivalence.StepCongr

@[expose] public section

namespace Std
open Std.Internal Std.Iterators

theorem IterM.stepAsHetT_filterMapWithPostcondition [Monad m] [LawfulMonad m] [Monad n]
    [LawfulMonad n] [Iterator α m β] [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → PostconditionT n (Option γ)} {it : IterM (α := α) m β} :
    (IterM.stepAsHetT (it.filterMapWithPostcondition f)) =
      (((IterM.stepAsHetT it).liftInner n : HetT n _)).bind (match · with
        | .yield it' out => do match ← HetT.ofPostconditionT (f out) with
          | some out' => return .yield (it'.filterMapWithPostcondition f) out'
          | none => return .skip (it'.filterMapWithPostcondition f)
        | .skip it' => return .skip (it'.filterMapWithPostcondition f)
        | .done => return .done) := by
  simp only [HetT.ext_iff, Equivalence.property_step, Equivalence.prun_step, HetT.prun_bind,
    HetT.property_liftInner, Equivalence.prun_liftInner_step, HetT.property_bind]
  refine ⟨?_, ?_⟩
  · ext step
    constructor
    · intro h
      cases h
      case yieldNone it' out h h' =>
        refine ⟨_, h, ?_⟩
        simp only [bind, HetT.property_bind, HetT.property_ofPostconditionT]
        exact ⟨none, by simp [Pure.pure]; exact ⟨h', rfl⟩⟩
      case yieldSome it' out out' h h' =>
        refine ⟨_, h, ?_⟩
        simp only [bind, HetT.property_bind, HetT.property_ofPostconditionT]
        exact ⟨some out', by simp [Pure.pure]; exact ⟨h', rfl⟩⟩
      case skip it' h =>
        exact ⟨_, h, by simp [Pure.pure]; rfl⟩
      case done h =>
        exact ⟨_, h, by simp [Pure.pure]⟩
    · rintro ⟨step', h, h'⟩
      cases step'
      case yield it' out =>
        simp only [bind, HetT.property_bind, HetT.property_ofPostconditionT] at h'
        rcases h' with ⟨out', h'⟩
        cases out'
        · simp only [pure, HetT.property_pure] at h'
          cases h'.2
          exact .yieldNone h h'.1
        · simp only [pure, HetT.property_pure] at h'
          cases h'.2
          exact .yieldSome h h'.1
      case skip it' =>
        simp only [pure, HetT.property_pure] at h'
        cases h'
        exact .skip h
      case done =>
        simp only [pure, HetT.property_pure] at h'
        cases h'
        exact .done h
  · intro β f
    simp only [IterM.step_filterMapWithPostcondition, PlausibleIterStep.skip,
      PlausibleIterStep.yield, PlausibleIterStep.done, bind_assoc]
    apply bind_congr
    intro step
    cases step.inflate using PlausibleIterStep.casesOn
    · simp only [bind_assoc, bind, HetT.prun_bind, HetT.prun_ofPostconditionT]
      apply bind_congr
      rintro ⟨out, _⟩
      cases out <;> simp [pure]
    · simp [pure]
    · simp [pure]

theorem IterM.Equiv.filterMapWithPostcondition {α₁ α₂ β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Iterator α₁ m β] [Iterator α₂ m β]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → PostconditionT n (Option γ)} {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    (h : IterM.Equiv ita itb) :
    IterM.Equiv (ita.filterMapWithPostcondition f) (itb.filterMapWithPostcondition f) := by
  rw [IterM.Equiv]
  refine BundledIterM.Equiv.coinduct n γ ?R ?implies (.ofIterM _) (.ofIterM _) ?hR
  case R =>
    intro ita' itb'
    exact ∃ (ita : IterM (α := α₁) m β) (itb : IterM (α := α₂) m β),
      ita' = .ofIterM (ita.filterMapWithPostcondition f) ∧
      itb' = .ofIterM (itb.filterMapWithPostcondition f) ∧
      IterM.Equiv ita itb
  case hR =>
    exact ⟨_, _, rfl, rfl, h⟩
  case implies =>
    rintro _ _ ⟨ita, itb, rfl, rfl, h'⟩
    replace h := h'
    simp only [BundledIterM.step, BundledIterM.iterator_ofIterM, HetT.map_eq_pure_bind,
      HetT.bind_assoc, Function.comp_apply, HetT.pure_bind, IterStep.mapIterator_mapIterator]
    rw [stepAsHetT_filterMapWithPostcondition, stepAsHetT_filterMapWithPostcondition]
    simp only [HetT.bind_assoc]
    simp only [Equiv, BundledIterM.Equiv, BundledIterM.step, BundledIterM.iterator_ofIterM,
      HetT.map_eq_pure_bind, HetT.bind_assoc, Function.comp_apply, HetT.pure_bind,
      IterStep.mapIterator_mapIterator] at h'
    apply liftInner_stepAsHetT_bind_congr h
    intro sa hsa sb hsb hs
    simp only [IterStep.bundledQuotient] at hs
    cases sa <;> cases sb <;> (try exfalso; simp_all; done)
    case yield =>
      simp only [IterStep.mapIterator_yield, Function.comp_apply, IterStep.yield.injEq,
        BundledIterM.Equiv.quotMk_eq_iff] at hs
      cases hs.2
      simp only [bind, HetT.bind_assoc]
      congr
      ext out
      cases out
      all_goals
        simp only [pure, HetT.pure_bind, IterStep.mapIterator_skip, IterStep.mapIterator_yield,
          Function.comp_apply]
        congr 2
        apply Quot.sound
        exact ⟨_, _, rfl, rfl, hs.1⟩
    case skip =>
      simp only [IterStep.mapIterator_skip, Function.comp_apply, IterStep.skip.injEq,
        BundledIterM.Equiv.quotMk_eq_iff] at hs
      simp only [pure, HetT.pure_bind, IterStep.mapIterator_skip, Function.comp_apply]
      congr 2
      apply Quot.sound
      exact ⟨_, _, rfl, rfl, hs⟩
    case done =>
      simp [Pure.pure]

theorem IterM.Equiv.filterWithPostcondition {α₁ α₂ β : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [Iterator α₁ m β] [Iterator α₂ m β]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → PostconditionT n (ULift Bool)} {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    (h : IterM.Equiv ita itb) :
    IterM.Equiv (ita.filterWithPostcondition f) (itb.filterWithPostcondition f) :=
  IterM.Equiv.filterMapWithPostcondition h

theorem IterM.Equiv.mapWithPostcondition {α₁ α₂ β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [Iterator α₁ m β] [Iterator α₂ m β]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → PostconditionT n γ} {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    (h : IterM.Equiv ita itb) :
    IterM.Equiv (ita.mapWithPostcondition f) (itb.mapWithPostcondition f) :=
  IterM.Equiv.filterMapWithPostcondition h

theorem IterM.Equiv.filterMapM {α₁ α₂ β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [Iterator α₁ m β] [Iterator α₂ m β]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → n (Option γ)} {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    (h : IterM.Equiv ita itb) :
    IterM.Equiv (ita.filterMapM f) (itb.filterMapM f) :=
  IterM.Equiv.filterMapWithPostcondition h

theorem IterM.Equiv.filterM {α₁ α₂ β : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [Iterator α₁ m β] [Iterator α₂ m β]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → n (ULift Bool)} {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    (h : IterM.Equiv ita itb) :
    IterM.Equiv (ita.filterM f) (itb.filterM f) :=
  IterM.Equiv.filterMapWithPostcondition h

theorem IterM.Equiv.mapM {α₁ α₂ β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} [Monad m] [LawfulMonad m]
    [Monad n] [MonadAttach n] [LawfulMonad n] [Iterator α₁ m β] [Iterator α₂ m β]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → n γ} {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    (h : IterM.Equiv ita itb) :
    IterM.Equiv (ita.mapM f) (itb.mapM f) :=
  IterM.Equiv.filterMapWithPostcondition h

theorem IterM.Equiv.filterMap {α₁ α₂ β γ : Type w}
    {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α₁ m β] [Iterator α₂ m β]
    {f : β → Option γ} {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    (h : IterM.Equiv ita itb) :
    IterM.Equiv (ita.filterMap f) (itb.filterMap f) :=
  IterM.Equiv.filterMapWithPostcondition h

theorem IterM.Equiv.filter {α₁ α₂ β : Type w}
    {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α₁ m β] [Iterator α₂ m β]
    {f : β → Bool} {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    (h : IterM.Equiv ita itb) :
    IterM.Equiv (ita.filter f) (itb.filter f) :=
  IterM.Equiv.filterMapWithPostcondition h

theorem IterM.Equiv.map {α₁ α₂ β γ : Type w}
    {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α₁ m β] [Iterator α₂ m β]
    {f : β → γ} {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    (h : IterM.Equiv ita itb) :
    IterM.Equiv (ita.map f) (itb.map f) :=
  IterM.Equiv.filterMapWithPostcondition h

end Std
