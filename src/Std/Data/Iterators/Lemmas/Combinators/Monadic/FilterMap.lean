/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Data.Iterators.Internal.LawfulMonadLiftFunction
import Std.Data.Iterators.Combinators.Monadic.FilterMap
import Init.Data.Iterators.Lemmas.Consumers.Monadic
import Std.Data.Iterators.Lemmas.Equivalence.StepCongr

namespace Std.Iterators
open Std.Internal

section Step

variable {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
  [Iterator α m β] {it : IterM (α := α) m β}

theorem IterM.step_filterMapWithPostcondition {f : β → PostconditionT n (Option β')}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.filterMapWithPostcondition f).step = (do
    match ← it.step with
    | .yield it' out h => do
      match ← (f out).operation with
      | ⟨none, h'⟩ =>
        pure <| .skip (it'.filterMapWithPostcondition f) (.yieldNone (out := out) h h')
      | ⟨some out', h'⟩ =>
        pure <| .yield (it'.filterMapWithPostcondition f) out' (.yieldSome (out := out) h h')
    | .skip it' h =>
      pure <| .skip (it'.filterMapWithPostcondition f) (.skip h)
    | .done h =>
      pure <| .done (.done h)) := by
  apply bind_congr
  intro step
  match step with
  | .yield it' out h =>
    simp only [PlausibleIterStep.skip, PlausibleIterStep.yield]
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem IterM.step_filterWithPostcondition {f : β → PostconditionT n (ULift Bool)}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.filterWithPostcondition f).step = (do
    match ← it.step with
    | .yield it' out h => do
      match ← (f out).operation with
      | ⟨.up false, h'⟩ =>
        pure <| .skip (it'.filterWithPostcondition f) (.yieldNone (out := out) h ⟨⟨_, h'⟩, rfl⟩)
      | ⟨.up true, h'⟩ =>
        pure <| .yield (it'.filterWithPostcondition f) out (.yieldSome (out := out) h ⟨⟨_, h'⟩, rfl⟩)
    | .skip it' h =>
      pure <| .skip (it'.filterWithPostcondition f) (.skip h)
    | .done h =>
      pure <| .done (.done h)) := by
  apply bind_congr
  intro step
  match step with
  | .yield it' out h =>
    simp only [PostconditionT.operation_map, PlausibleIterStep.skip, PlausibleIterStep.yield,
      bind_map_left]
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem IterM.step_mapWithPostcondition {γ : Type w} {f : β → PostconditionT n γ}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.mapWithPostcondition f).step = (do
    match ← it.step with
    | .yield it' out h => do
      let out' ← (f out).operation
      pure <| .yield (it'.mapWithPostcondition f) out'.1 (.yieldSome h ⟨out', rfl⟩)
    | .skip it' h =>
      pure <| .skip (it'.mapWithPostcondition f) (.skip h)
    | .done h =>
      pure <| .done (.done h)) := by
  apply bind_congr
  intro step
  match step with
  | .yield it' out h =>
    simp only [PostconditionT.operation_map, bind_map_left, bind_pure_comp]
    rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem IterM.step_filterMapM {f : β → n (Option β')}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.filterMapM f).step = (do
    match ← it.step with
    | .yield it' out h => do
      match ← f out with
      | none =>
        pure <| .skip (it'.filterMapM f) (.yieldNone (out := out) h .intro)
      | some out' =>
        pure <| .yield (it'.filterMapM f) out' (.yieldSome (out := out) h .intro)
    | .skip it' h =>
      pure <| .skip (it'.filterMapM f) (.skip h)
    | .done h =>
      pure <| .done (.done h)) := by
  apply bind_congr
  intro step
  match step with
  | .yield it' out h =>
    simp only [PostconditionT.lift, bind_map_left]
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem IterM.step_filterM {f : β → n (ULift Bool)}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.filterM f).step = (do
    match ← it.step with
    | .yield it' out h => do
      match ← f out with
      | .up false =>
        pure <| .skip (it'.filterM f) (.yieldNone (out := out) h ⟨⟨.up false, .intro⟩, rfl⟩)
      | .up true =>
        pure <| .yield (it'.filterM f) out (.yieldSome (out := out) h ⟨⟨.up true, .intro⟩, rfl⟩)
    | .skip it' h =>
      pure <| .skip (it'.filterM f) (.skip h)
    | .done h =>
      pure <| .done (.done h)) := by
  apply bind_congr
  intro step
  match step with
  | .yield it' out h =>
    simp only [PostconditionT.lift, 
      PostconditionT.operation_map, Functor.map_map, PlausibleIterStep.skip,
      PlausibleIterStep.yield, bind_map_left]
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem IterM.step_mapM {γ : Type w} {f : β → n γ}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.mapM f).step = (do
    match ← it.step with
    | .yield it' out h => do
      let out' ← f out
      pure <| .yield (it'.mapM f) out' (.yieldSome h ⟨⟨out', True.intro⟩, rfl⟩)
    | .skip it' h =>
      pure <| .skip (it'.mapM f) (.skip h)
    | .done h =>
      pure <| .done (.done h)) := by
  apply bind_congr
  intro step
  match step with
  | .yield it' out h =>
    simp only [bind_pure_comp]
    simp only [PostconditionT.lift, Functor.map, 
      ]
    simp only [PostconditionT.operation_map, Functor.map_map, PlausibleIterStep.skip,
      PlausibleIterStep.yield, bind_map_left, bind_pure_comp]
    rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem IterM.step_filterMap [Monad m] [LawfulMonad m] {f : β → Option β'} :
  (it.filterMap f).step = (do
    match ← it.step with
    | .yield it' out h => do
      match h' : f out with
      | none =>
        pure <| .skip (it'.filterMap f) (.yieldNone h h')
      | some out' =>
        pure <| .yield (it'.filterMap f) out' (.yieldSome h h')
    | .skip it' h =>
      pure <| .skip (it'.filterMap f) (.skip h)
    | .done h =>
      pure <| .done (.done h)) := by
  simp only [IterM.filterMap, step_filterMapWithPostcondition, pure]
  apply bind_congr
  intro step
  split
  · simp only [PostconditionT.pure, PlausibleIterStep.skip, PlausibleIterStep.yield, pure_bind]
    split <;> split <;> simp_all
  · simp
  · simp

theorem IterM.step_map [Monad m] [LawfulMonad m] {f : β → β'} :
  (it.map f).step = (do
    match ← it.step with
    | .yield it' out h =>
      let out' := f out
      pure <| .yield (it'.map f) out' (.yieldSome h ⟨⟨out', rfl⟩, rfl⟩)
    | .skip it' h =>
      pure <| .skip (it'.map f) (.skip h)
    | .done h => pure <| .done (.done h)) := by
  simp only [map, IterM.step_mapWithPostcondition]
  apply bind_congr
  intro step
  split
  · simp
  · rfl
  · rfl

theorem IterM.step_filter [Monad m] [LawfulMonad m] {f : β → Bool} :
  (it.filter f).step = (do
    match ← it.step with
    | .yield it' out h =>
      if h' : f out = true then
        pure <| .yield (it'.filter f) out (.yieldSome h (by simp [h']))
      else
        pure <| .skip (it'.filter f) (.yieldNone h (by simp [h']))
    | .skip it' h =>
      pure <| .skip (it'.filter f) (.skip h)
    | .done h => pure <| .done (.done h)) := by
  simp only [filter, IterM.step_filterMap]
  apply bind_congr
  intro step
  split
  · split
    · split
      · exfalso; simp_all
      · rfl
    · split
      · congr; simp_all
      · exfalso; simp_all
  · rfl
  · rfl

end Step

section Lawful

instance {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type x}
    [Monad m] [Monad n] [Monad o] [LawfulMonad n] [LawfulMonad o] [Iterator α m β] [Finite α m]
    [IteratorCollect α m o] [LawfulIteratorCollect α m o]
    {lift : ⦃δ : Type w⦄ -> m δ → n δ} {f : β → PostconditionT n γ} [LawfulMonadLiftFunction lift] :
    LawfulIteratorCollect (Map α m n lift f) n o where
  lawful_toArrayMapped := by
    intro δ lift' _ _
    letI : MonadLift m n := ⟨lift (δ := _)⟩
    letI : MonadLift n o := ⟨lift' (α := _)⟩
    ext g it
    have : it = IterM.mapWithPostcondition _ it.internalState.inner := by rfl
    generalize it.internalState.inner = it at *
    cases this
    simp only [LawfulIteratorCollect.toArrayMapped_eq]
    simp only [IteratorCollect.toArrayMapped]
    rw [LawfulIteratorCollect.toArrayMapped_eq]
    induction it using IterM.inductSteps with | step it ih_yield ih_skip =>
    rw [IterM.DefaultConsumers.toArrayMapped_eq_match_step]
    rw [IterM.DefaultConsumers.toArrayMapped_eq_match_step]
    simp only [bind_assoc]
    rw [IterM.step_mapWithPostcondition]
    simp only [liftM_bind (m := n) (n := o), bind_assoc]
    apply bind_congr
    intro step
    split
    · simp only [bind_pure_comp]
      simp only [liftM_map, bind_map_left]
      apply bind_congr
      intro out'
      simp only [← ih_yield ‹_›]
      rfl
    · simp only [bind_pure_comp, pure_bind, liftM_pure, pure_bind, ← ih_skip ‹_›]
      simp only [IterM.mapWithPostcondition, IterM.InternalCombinators.map, internalState_toIterM]
    · simp

end Lawful

section ToList

theorem IterM.InternalConsumers.toList_filterMap {α β γ: Type w} {m : Type w → Type w'}
    [Monad m] [LawfulMonad m]
    [Iterator α m β] [IteratorCollect α m m] [LawfulIteratorCollect α m m] [Finite α m]
    {f : β → Option γ} (it : IterM (α := α) m β) :
    (it.filterMap f).toList = (fun x => x.filterMap f) <$> it.toList := by
  induction it using IterM.inductSteps
  rename_i it ihy ihs
  rw [IterM.toList_eq_match_step, IterM.toList_eq_match_step]
  simp only [bind_pure_comp, map_bind]
  rw [step_filterMap]
  simp only [bind_assoc, IterM.step, map_eq_pure_bind]
  apply bind_congr
  intro step
  split
  · simp only [List.filterMap_cons, bind_assoc, pure_bind]
    split
    · split
      · simp only [bind_pure_comp, pure_bind]
        exact ihy ‹_›
      · simp_all
    · split
      · simp_all
      · simp_all [ihy ‹_›]
  · simp only [bind_pure_comp, pure_bind]
    apply ihs
    assumption
  · simp

theorem IterM.toList_filterMap {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [LawfulMonad m]
    [Iterator α m β] [IteratorCollect α m m] [LawfulIteratorCollect α m m] [Finite α m]
    {f : β → Option γ} (it : IterM (α := α) m β) :
    (it.filterMap f).toList = (fun x => x.filterMap f) <$> it.toList := by
  induction it using IterM.inductSteps
  rename_i it ihy ihs
  rw [IterM.toList_eq_match_step, IterM.toList_eq_match_step]
  simp only [bind_pure_comp, map_bind]
  rw [step_filterMap]
  simp only [bind_assoc, IterM.step, map_eq_pure_bind]
  apply bind_congr
  intro step
  split
  · simp only [List.filterMap_cons, bind_assoc, pure_bind]
    split
    · split
      · simp only [bind_pure_comp, pure_bind]
        exact ihy ‹_›
      · simp_all
    · split
      · simp_all
      · simp_all [ihy ‹_›]
  · simp only [bind_pure_comp, pure_bind]
    apply ihs
    assumption
  · simp

theorem IterM.toList_map {α β β' : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α m β] [IteratorCollect α m m] [LawfulIteratorCollect α m m] [Finite α m] {f : β → β'}
    (it : IterM (α := α) m β) :
    (it.map f).toList = (fun x => x.map f) <$> it.toList := by
  rw [LawfulIteratorCollect.toList_eq, ← List.filterMap_eq_map, ← toList_filterMap]
  let t := type_of% (it.map f)
  let t' := type_of% (it.filterMap (some ∘ f))
  congr
  · simp [Map]
  · simp [instIteratorMap, inferInstanceAs]
    congr
    simp
  · refine heq_of_eqRec_eq ?_ rfl
    congr
    simp only [Map, PostconditionT.map_pure, Function.comp_apply]
    simp only [instIteratorMap, inferInstanceAs, Function.comp_apply]
    congr
    simp
  · simp [Map]
  · simp only [instIteratorMap, inferInstanceAs, Function.comp_apply]
    congr
    simp
  · simp only [map, mapWithPostcondition, InternalCombinators.map, Function.comp_apply, filterMap,
    filterMapWithPostcondition, InternalCombinators.filterMap]
    congr
    · simp [Map]
    · simp

theorem IterM.toList_filter {α : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {β : Type w} [Iterator α m β] [Finite α m] [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {f : β → Bool} {it : IterM (α := α) m β} :
    (it.filter f).toList = List.filter f <$> it.toList := by
  simp only [filter, toList_filterMap, ← List.filterMap_eq_filter]
  rfl

end ToList

section ToListRev

theorem IterM.toListRev_filterMap {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [LawfulMonad m]
    [Iterator α m β] [IteratorCollect α m m] [LawfulIteratorCollect α m m] [Finite α m]
    {f : β → Option γ} (it : IterM (α := α) m β) :
    (it.filterMap f).toListRev = (fun x => x.filterMap f) <$> it.toListRev := by
  simp [toListRev_eq, toList_filterMap]

theorem IterM.toListRev_map {α β γ : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α m β] [IteratorCollect α m m] [LawfulIteratorCollect α m m] [Finite α m] {f : β → γ}
    (it : IterM (α := α) m β) :
    (it.map f).toListRev = (fun x => x.map f) <$> it.toListRev := by
  simp [toListRev_eq, toList_map]

theorem IterM.toListRev_filter {α β : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {f : β → Bool} {it : IterM (α := α) m β} :
    (it.filter f).toListRev = List.filter f <$> it.toListRev := by
  simp [toListRev_eq, toList_filter]

end ToListRev

section ToArray

theorem IterM.toArray_filterMap {α β γ : Type w} {m : Type w → Type w'}
    [Monad m] [LawfulMonad m]
    [Iterator α m β] [IteratorCollect α m m] [LawfulIteratorCollect α m m] [Finite α m]
    {f : β → Option γ} (it : IterM (α := α) m β) :
    (it.filterMap f).toArray = (fun x => x.filterMap f) <$> it.toArray := by
  simp [← toArray_toList, toList_filterMap]

theorem IterM.toArray_map {α β γ : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α m β] [IteratorCollect α m m] [LawfulIteratorCollect α m m] [Finite α m] {f : β → γ}
    (it : IterM (α := α) m β) :
    (it.map f).toArray = (fun x => x.map f) <$> it.toArray := by
  simp [← toArray_toList, toList_map]

theorem IterM.toArray_filter {α : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {β : Type w} [Iterator α m β] [Finite α m] [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {f : β → Bool} {it : IterM (α := α) m β} :
    (it.filter f).toArray = Array.filter f <$> it.toArray := by
  simp [← toArray_toList, toList_filter]

end ToArray

section Equivalence

theorem stepAsHetT_filterMapWithPostcondition [Monad m] [LawfulMonad m] [Monad n]
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
    cases step using PlausibleIterStep.casesOn
    · simp only [bind_assoc, bind, HetT.prun_bind, HetT.property_ofPostconditionT,
        HetT.prun_ofPostconditionT]
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
  refine BundledIterM.Equiv.fixpoint_induct n γ ?R ?implies (.ofIterM _) (.ofIterM _) ?hR
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
    [Monad n] [LawfulMonad n] [Iterator α₁ m β] [Iterator α₂ m β]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → n (Option γ)} {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    (h : IterM.Equiv ita itb) :
    IterM.Equiv (ita.filterMapM f) (itb.filterMapM f) :=
  IterM.Equiv.filterMapWithPostcondition h

theorem IterM.Equiv.filterM {α₁ α₂ β : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [Iterator α₁ m β] [Iterator α₂ m β]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → n (ULift Bool)} {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    (h : IterM.Equiv ita itb) :
    IterM.Equiv (ita.filterM f) (itb.filterM f) :=
  IterM.Equiv.filterMapWithPostcondition h

theorem IterM.Equiv.mapM {α₁ α₂ β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [Iterator α₁ m β] [Iterator α₂ m β]
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

end Equivalence

end Std.Iterators
