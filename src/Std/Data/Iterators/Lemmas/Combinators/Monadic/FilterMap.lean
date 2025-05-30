/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Internal.LawfulMonadLiftFunction
import Std.Data.Iterators.Combinators.Monadic.FilterMap
import Std.Data.Iterators.Lemmas.Consumers.Monadic
import Std.Data.Iterators.Lemmas.Equivalence.Advanced

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
    simp only [PostconditionT.lift, liftM, monadLift, MonadLift.monadLift, monadLift_self,
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
    simp only [PostconditionT.operation_map, bind_map_left, bind_pure_comp]
    simp only [PostconditionT.lift, Functor.map, Functor.map_map,
      bind_map_left, bind_pure_comp]
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
  · simp [pure_bind, PostconditionT.pure]
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
    · simp only [bind_pure_comp, bind_map_left, ← ih_yield ‹_›]
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
  · simp only [List.filterMap_cons, bind_assoc, pure_bind, bind_pure]
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
  · simp only [List.filterMap_cons, bind_assoc, pure_bind, bind_pure]
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

theorem step'_filterMapM [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Iterator α m β]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → n (Option γ)} {it : IterM (α := α) m β} :
    (it.filterMapM f).step' = ((it.step'.liftInner n : HetT n _)).bind (match · with
      | .yield it' out => do match ← HetT.lift (f out) with
        | some out' => return .yield (it'.filterMapM f) out'
        | none => return .skip (it'.filterMapM f)
      | .skip it' => return .skip (it'.filterMapM f)
      | .done => return .done) := by
  simp [HetT.ext_iff]
  refine ⟨?_, ?_⟩
  · ext step
    constructor
    · intro h
      cases h
      case yieldNone it' out h h' =>
        refine ⟨_, h, ?_⟩
        simp [Bind.bind]
        exact ⟨none, by simp [Pure.pure]; rfl⟩
      case yieldSome it' out out' h h' =>
        refine ⟨_, h, ?_⟩
        simp [Bind.bind]
        exact ⟨some out', by simp [Pure.pure]; rfl⟩
      case skip it' h =>
        exact ⟨_, h, by simp [Pure.pure]; rfl⟩
      case done h =>
        exact ⟨_, h, by simp [Pure.pure]⟩
    · rintro ⟨step', h, h'⟩
      cases step'
      case yield it' out =>
        simp [Bind.bind] at h'
        rcases h' with ⟨out', h'⟩
        cases out'
        · simp [Pure.pure] at h'
          cases h'
          exact .yieldNone h .intro
        · simp [Pure.pure] at h'
          cases h'
          exact .yieldSome h .intro
      case skip it' =>
        simp [Bind.bind, Pure.pure] at h'
        cases h'
        exact .skip h
      case done =>
        simp [Bind.bind, Pure.pure] at h'
        cases h'
        exact .done h
  · intro β f
    simp [IterM.step_filterMapM]
    apply bind_congr
    intro step
    cases step using PlausibleIterStep.casesOn
    · simp [Bind.bind, HetT.prun_bind]
      apply bind_congr
      intro out
      cases out <;> simp [pure]
    · simp [pure]
    · simp [pure]

theorem HItEquivM.liftInner_step'_pbind_congr [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [Iterator α₁ m β] [Iterator α₂ m β]
    {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    {f : (_ : _) → _ → HetT n γ} {g : (_ : _) → _ → HetT n γ} (h : HItEquivM ita itb)
    (hfg : ∀ sa hsa sb hsb, sa.bundle = sb.bundle → f sa hsa = g sb hsb) :
    (ita.step'.liftInner n).pbind f = (itb.step'.liftInner n).pbind g := by
  simp [HetT.ext_iff]
  refine ⟨?_, ?_⟩
  · ext c
    constructor
    · rintro ⟨s₁, hs₁, hf⟩
      rcases exists_equiv_step h ⟨s₁, hs₁⟩ with ⟨s₂, h'⟩
      exact ⟨s₂.1, s₂.2, (hfg s₁ hs₁ s₂.1 s₂.2 h') ▸ hf⟩
    · rintro ⟨s₁, hs₁, hf⟩
      rcases exists_equiv_step h.symm ⟨s₁, hs₁⟩ with ⟨s₂, h'⟩
      exact ⟨s₂.1, s₂.2, (hfg s₂.1 s₂.2 s₁ hs₁ h'.symm) ▸ hf⟩
  · intro γ l
    apply step_congr h
    intro s₁ s₂ h
    simp only [hfg s₁.1 s₁.2 s₂.1 s₂.2 h]

theorem HItEquivM.liftInner_step'_bind_congr [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] [Iterator α₁ m β] [Iterator α₂ m β]
    {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    {f : (_ : _) → HetT n γ} {g : (_ : _) → HetT n γ} (h : HItEquivM ita itb)
    (hfg : ∀ sa (_ : ita.step'.Property sa) sb (_ : itb.step'.Property sb), sa.bundle = sb.bundle → f sa = g sb) :
    (ita.step'.liftInner n).bind f = (itb.step'.liftInner n).bind g := by
  simp [HetT.bind_eq_pbind]
  apply liftInner_step'_pbind_congr h
  exact hfg

theorem HItEquivM.filterMapM [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [Iterator α₁ m β] [Iterator α₂ m β]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → n (Option γ)} {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    (h : HItEquivM ita itb) :
    HItEquivM (ita.filterMapM f) (itb.filterMapM f) := by
  rw [HItEquivM]
  refine ItEquiv.fixpoint_induct n γ ?R ?implies (.ofIterM _) (.ofIterM _) ?hR
  case R =>
    intro ita' itb'
    exact ∃ (ita : IterM (α := α₁) m β) (itb : IterM (α := α₂) m β),
      ita' = .ofIterM (ita.filterMapM f) ∧
      itb' = .ofIterM (itb.filterMapM f) ∧
      HItEquivM ita itb
  case hR =>
    exact ⟨_, _, rfl, rfl, h⟩
  case implies =>
    rintro _ _ ⟨ita, itb, rfl, rfl, h'⟩
    replace h := h'
    simp [BundledIterM.step']
    rw [step'_filterMapM, step'_filterMapM]
    simp
    simp [HItEquivM, ItEquiv, BundledIterM.step'] at h'
    apply liftInner_step'_bind_congr h
    intro sa hsa sb hsb hs
    simp [IterStep.bundle] at hs
    cases sa <;> cases sb <;> (try exfalso; simp_all; done)
    case yield =>
      simp [ItEquiv.quotMk_eq_iff] at hs
      cases hs.2
      simp [bind_assoc, Bind.bind]
      congr
      ext out
      cases out
      all_goals
        simp [Pure.pure]
        congr 2
        apply Quot.sound
        exact ⟨_, _, rfl, rfl, hs.1⟩
    case skip =>
      simp [ItEquiv.quotMk_eq_iff] at hs
      simp [Pure.pure]
      congr 2
      apply Quot.sound
      exact ⟨_, _, rfl, rfl, hs⟩
    case done =>
      simp [Pure.pure]

theorem HItEquivM.InternalCombinators.filterMap [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [Iterator α₁ m β] [Iterator α₂ m β]
    {lift} [LawfulMonadLiftFunction lift]
    {f : β → PostconditionT n (Option γ)} {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    (h : HItEquivM ita itb) :
    HItEquivM (IterM.InternalCombinators.filterMap lift f ita)
      (IterM.InternalCombinators.filterMap lift f itb) := by
  letI i : MonadLift m n := ⟨lift (α := _)⟩
  change HItEquivM (ita.filterMapWithProof f) (itb.filterMapWithProof f)
  rw [HItEquivM]
  refine ItEquiv.fixpoint_induct n γ ?R ?implies (.ofIterM _) (.ofIterM _) ?hf
  case R =>
    intro ita' itb'
    exact ∃ (ita : IterM (α := α₁) m β) (itb : IterM (α := α₂) m β),
      ita' = .ofIterM (ita.filterMapWithProof f) ∧
      itb' = .ofIterM (itb.filterMapWithProof f) ∧
      HItEquivM ita itb
  case implies =>
    rintro _ _ ⟨ita, itb, rfl, rfl, h⟩
    simp? [BundledIterM.step', test]


theorem HItEquivM.InternalCombinators.filterMap [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [Iterator α₁ m β] [Iterator α₂ m β]
    {lift} [LawfulMonadLiftFunction lift]
    {f : β → PostconditionT n (Option γ)} {ita : IterM (α := α₁) m β} {itb : IterM (α := α₂) m β}
    (h : HItEquivM ita itb) :
    HItEquivM (IterM.InternalCombinators.filterMap lift f ita)
      (IterM.InternalCombinators.filterMap lift f itb) := by
  letI i : MonadLift m n := ⟨lift (α := _)⟩
  change HItEquivM (ita.filterMapWithPostcondition f) (itb.filterMapWithPostcondition f)
  rw [HItEquivM]
  refine ItEquiv.fixpoint_induct n γ ?R ?implies (.ofIterM _) (.ofIterM _) ?hf
  case R =>
    intro ita' itb'
    exact ∃ (ita : IterM (α := α₁) m β) (itb : IterM (α := α₂) m β),
      ita' = .ofIterM (ita.filterMapWithPostcondition f) ∧
      itb' = .ofIterM (itb.filterMapWithPostcondition f) ∧
      HItEquivM ita itb
  case implies =>
    rintro _ _ ⟨ita, itb, rfl, rfl, h⟩
    simp only [BundledIterM.step', BundledIterM.ofIterM, IterM.step', IterM.step_filterMapWithPostcondition]
    simp only [HetT.ext_iff]
    refine ⟨?_, ?_⟩
    · simp [HetT.bind, Pure.pure, HetT.pure]
      ext step
      constructor
      · rintro ⟨step', hp, rfl⟩
        rw [HItEquivM, ItEquiv] at h
        replace h := congrArg HetT.Property h
        simp [BundledIterM.step', HetT.bind, Pure.pure, HetT.pure, funext_iff] at h
        cases hp
        case yieldNone it' out h' h'' =>
          simp [IterM.filterMapWithPostcondition, IterM.InternalCombinators.filterMap] at h'
          specialize h (IterStep.yield it' out).bundle
          replace h := h.1 ⟨.yield it' out, h', rfl⟩
          rcases h with ⟨sb, hpb, hsb⟩
          cases sb <;> simp only [IterStep.mapIterator, Function.comp_apply, IterStep.bundle,
            reduceCtorEq, IterStep.yield.injEq] at hsb
          rename_i itb outb
          cases hsb.2
          refine ⟨.skip (itb.filterMapWithPostcondition f), .yieldNone hpb h'', ?_⟩
          simp
          apply Eq.symm
          apply Quot.sound
          refine ⟨it', itb, rfl, rfl, ?_⟩
          have := ItEquiv.exact _ _ hsb.1
          exact this.symm
        case yieldSome => sorry
        case skip => sorry
        case done => sorry
      · sorry -- just the same proofs again?
    · intro γ f
      simp [HetT.map]
      apply h.step_congr -- d'oh, `liftM` again
      -- btw, I'd probably need a step_congr for this special relation R
      -- will all this become easier if I characerize step' for this iterator in terms of
      -- the inner step'?
  case hf =>
    exact ⟨ita, itb, rfl, rfl, h⟩


end Equivalence

end Std.Iterators
