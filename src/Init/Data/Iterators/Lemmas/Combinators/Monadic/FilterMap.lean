/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Internal.LawfulMonadLiftFunction
public import Init.Data.Iterators.Combinators.Monadic.FilterMap
public import Init.Data.Iterators.Lemmas.Consumers.Monadic
public import Init.Data.Iterators.Consumers.Monadic.Collect
import all Init.Data.Iterators.Consumers.Monadic.Collect

public section

namespace Std.Iterators
open Std.Internal

section Step

variable {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
  [Iterator α m β] {it : IterM (α := α) m β}

theorem IterM.step_filterMapWithPostcondition {f : β → PostconditionT n (Option β')}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.filterMapWithPostcondition f).step = (do
    match (← it.step).inflate with
    | .yield it' out h => do
      match ← (f out).operation with
      | ⟨none, h'⟩ =>
        pure <| .deflate <| .skip (it'.filterMapWithPostcondition f) (.yieldNone (out := out) h h')
      | ⟨some out', h'⟩ =>
        pure <| .deflate <| .yield (it'.filterMapWithPostcondition f) out' (.yieldSome (out := out) h h')
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.filterMapWithPostcondition f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (by exact .done h)) := by
  apply bind_congr
  intro step
  match step.inflate with
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
    match (← it.step).inflate with
    | .yield it' out h => do
      match ← (f out).operation with
      | ⟨.up false, h'⟩ =>
        pure <| .deflate <| .skip (it'.filterWithPostcondition f) (.yieldNone (out := out) h ⟨⟨_, h'⟩, rfl⟩)
      | ⟨.up true, h'⟩ =>
        pure <| .deflate <| .yield (it'.filterWithPostcondition f) out (by exact .yieldSome (out := out) h ⟨⟨_, h'⟩, rfl⟩)
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.filterWithPostcondition f) (by exact .skip h)
    | .done h =>
      pure <| .deflate <| .done (by exact .done h)) := by
  apply bind_congr
  intro step
  match step.inflate with
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
    match (← it.step).inflate with
    | .yield it' out h => do
      let out' ← (f out).operation
      pure <| .deflate <| .yield (it'.mapWithPostcondition f) out'.1 (.yieldSome h ⟨out', rfl⟩)
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.mapWithPostcondition f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (.done h)) := by
  apply bind_congr
  intro step
  match step.inflate with
  | .yield it' out h =>
    simp only [PostconditionT.operation_map, bind_map_left, bind_pure_comp]
    rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem IterM.step_filterMapM {f : β → n (Option β')}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.filterMapM f).step = (do
    match (← it.step).inflate with
    | .yield it' out h => do
      match ← f out with
      | none =>
        pure <| .deflate <| .skip (it'.filterMapM f) (.yieldNone (out := out) h .intro)
      | some out' =>
        pure <| .deflate <| .yield (it'.filterMapM f) out' (.yieldSome (out := out) h .intro)
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.filterMapM f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (.done h)) := by
  apply bind_congr
  intro step
  match step.inflate with
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
    match (← it.step).inflate with
    | .yield it' out h => do
      match ← f out with
      | .up false =>
        pure <| .deflate <| .skip (it'.filterM f) (.yieldNone (out := out) h ⟨⟨.up false, .intro⟩, rfl⟩)
      | .up true =>
        pure <| .deflate <| .yield (it'.filterM f) out (.yieldSome (out := out) h ⟨⟨.up true, .intro⟩, rfl⟩)
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.filterM f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (.done h)) := by
  apply bind_congr
  intro step
  match step.inflate with
  | .yield it' out h =>
    simp only [PostconditionT.lift, PostconditionT.operation_map, Functor.map_map,
      PlausibleIterStep.skip, PlausibleIterStep.yield, bind_map_left]
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem IterM.step_mapM {γ : Type w} {f : β → n γ}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.mapM f).step = (do
    match (← it.step).inflate with
    | .yield it' out h => do
      let out' ← f out
      pure <| .deflate <| .yield (it'.mapM f) out' (.yieldSome h ⟨⟨out', True.intro⟩, rfl⟩)
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.mapM f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (.done h)) := by
  apply bind_congr
  intro step
  match step.inflate with
  | .yield it' out h =>
    simp only [bind_pure_comp]
    simp only [PostconditionT.lift]
    simp only [PostconditionT.operation_map, Functor.map_map, PlausibleIterStep.skip,
      PlausibleIterStep.yield, bind_map_left, bind_pure_comp]
    rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem IterM.step_filterMap [Monad m] [LawfulMonad m] {f : β → Option β'} :
  (it.filterMap f).step = (do
    match (← it.step).inflate with
    | .yield it' out h => do
      match h' : f out with
      | none =>
        pure <| .deflate <| .skip (it'.filterMap f) (.yieldNone h h')
      | some out' =>
        pure <| .deflate <| .yield (it'.filterMap f) out' (.yieldSome h h')
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.filterMap f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (.done h)) := by
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
    match (← it.step).inflate with
    | .yield it' out h =>
      let out' := f out
      pure <| .deflate <| .yield (it'.map f) out' (.yieldSome h ⟨⟨out', rfl⟩, rfl⟩)
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.map f) (.skip h)
    | .done h => pure <| .deflate <| .done (.done h)) := by
  simp only [map, IterM.step_mapWithPostcondition]
  apply bind_congr
  intro step
  split
  · simp
  · rfl
  · rfl

theorem IterM.step_filter [Monad m] [LawfulMonad m] {f : β → Bool} :
  (it.filter f).step = (do
    match (← it.step).inflate with
    | .yield it' out h =>
      if h' : f out = true then
        pure <| .deflate <| .yield (it'.filter f) out (.yieldSome h (by simp [h']))
      else
        pure <| .deflate <| .skip (it'.filter f) (.yieldNone h (by simp [h']))
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.filter f) (.skip h)
    | .done h => pure <| .deflate <| .done (.done h)) := by
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

@[no_expose]
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
    induction it using IterM.inductSteps with | step it ih_yield ih_skip
    rw [IterM.DefaultConsumers.toArrayMapped_eq_match_step]
    rw [IterM.DefaultConsumers.toArrayMapped_eq_match_step]
    simp only [bind_assoc]
    rw [IterM.step_mapWithPostcondition]
    simp only [liftM_bind (m := n) (n := o), bind_assoc]
    apply bind_congr
    intro step
    cases step.inflate using PlausibleIterStep.casesOn
    · simp only [bind_pure_comp]
      simp only [liftM_map, bind_map_left]
      apply bind_congr
      intro out'
      simp only [Shrink.inflate_deflate, ← ih_yield ‹_›]
      rfl
    · simp only [bind_pure_comp, pure_bind, liftM_pure, pure_bind, ← ih_skip ‹_›,
        Shrink.inflate_deflate]
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
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [List.filterMap_cons, bind_assoc, pure_bind]
    split <;> simp (discharger := assumption) [*]
  · simp [ihs ‹_›]
  · simp

theorem IterM.toList_map_eq_toList_mapM {α β γ : Type w}
    {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {f : β → γ} {it : IterM (α := α) m β} :
    (it.map f).toList = (it.mapM fun b => pure (f b)).toList := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [toList_eq_match_step, toList_eq_match_step, step_map, step_mapM, bind_assoc, bind_assoc]
  apply bind_congr; intro step
  split <;> simp (discharger := assumption) [ihy, ihs]

theorem IterM.toList_mapM_eq_toList_filterMapM {α β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n][LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m] [IteratorCollect α m n] [LawfulIteratorCollect α m n]
    {f : β → n γ} {it : IterM (α := α) m β} :
    (it.mapM f).toList =
      (it.filterMapM fun b => some <$> f b).toList := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [toList_eq_match_step, toList_eq_match_step, step_mapM, step_filterMapM, bind_assoc, bind_assoc]
  apply bind_congr; intro step
  split <;> simp (discharger := assumption) [ihy, ihs]

theorem IterM.toList_map_eq_toList_filterMapM {α β γ : Type w}
    {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {f : β → γ} {it : IterM (α := α) m β} :
    (it.map f).toList = (it.filterMapM fun b => pure (some (f b))).toList := by
  simp [toList_map_eq_toList_mapM, toList_mapM_eq_toList_filterMapM]
  congr <;> simp

@[simp]
theorem IterM.toList_filterMapM_filterMapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m] [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {f : β → n (Option γ)} {g : γ → o (Option δ)}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.filterMapM f).filterMapM g).toList =
      (it.filterMapM (n := o) (fun b => do
        match ← f b with
        | none => return none
        | some fb => g fb)).toList := by
  induction it using IterM.inductSteps with | step it ihy ihs
  letI : MonadLift n o := ⟨monadLift⟩
  haveI : LawfulMonadLift n o := ⟨by simp [this], by simp [this]⟩
  rw [toList_eq_match_step, toList_eq_match_step, step_filterMapM,
    bind_assoc, step_filterMapM, step_filterMapM]
  simp only [bind_assoc, liftM_bind]
  apply bind_congr; intro step
  split
  · simp only [bind_assoc, liftM_bind]
    apply bind_congr; intro fx
    split
    · simp [ihy ‹_›]
    · simp only [liftM_pure, PlausibleIterStep.skip, pure_bind, bind_assoc, Shrink.inflate_deflate]
      apply bind_congr; intro gx
      split <;> simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

@[simp]
theorem IterM.toList_filterMapM_mapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → n γ} {g : γ → o (Option δ)}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.mapM f).filterMapM g).toList =
      (it.filterMapM (n := o) (fun b => do g (← f b))).toList := by
  induction it using IterM.inductSteps with | step it ihy ihs
  letI : MonadLift n o := ⟨monadLift⟩
  haveI : LawfulMonadLift n o := ⟨by simp [this], by simp [this]⟩
  rw [toList_eq_match_step, toList_eq_match_step, step_filterMapM,
    bind_assoc, step_filterMapM, step_mapM]
  simp only [bind_assoc, liftM_bind]
  apply bind_congr; intro step
  split
  · simp only [bind_assoc, liftM_bind]
    apply bind_congr; intro fx
    simp only [liftM_pure, pure_bind, bind_assoc, Shrink.inflate_deflate]
    apply bind_congr; intro gx
    split <;> simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

@[simp]
theorem IterM.toList_filterMapM_map {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m]
    {f : β → γ} {g : γ → n (Option δ)}
    {it : IterM (α := α) m β} :
    ((it.map f).filterMapM g).toList =
      (it.filterMapM (n := n) (fun b => g (f b))).toList := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [toList_eq_match_step, toList_eq_match_step, step_filterMapM,
    bind_assoc, step_filterMapM, step_map]
  simp only [bind_assoc, liftM_bind]
  apply bind_congr; intro step
  split
  · simp only [bind_assoc, liftM_pure, pure_bind, Shrink.inflate_deflate]
    apply bind_congr; intro fx
    split <;> simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

@[simp]
theorem IterM.toList_mapM_filterMapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m] [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {f : β → n (Option γ)} {g : γ → o δ}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.filterMapM f).mapM g).toList =
      (it.filterMapM (n := o) (fun b => do
        match ← f b with
        | none => return none
        | some fb => some <$> g fb)).toList := by
  simp [toList_mapM_eq_toList_filterMapM, toList_filterMapM_filterMapM]

@[simp]
theorem IterM.toList_mapM_mapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m] [IteratorCollect α m o] [LawfulIteratorCollect α m o]
    {f : β → n γ} {g : γ → o δ}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.mapM f).mapM g).toList =
      (it.mapM (n := o) (fun b => do g (← f b))).toList := by
  simp only [toList_mapM_eq_toList_filterMapM, toList_filterMapM_mapM]
  congr <;> simp

@[simp]
theorem IterM.toList_mapM_map {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m] [IteratorCollect α m n] [LawfulIteratorCollect α m n]
    {f : β → γ} {g : γ → n δ}
    {it : IterM (α := α) m β} :
    ((it.map f).mapM g).toList =
      (it.mapM (n := n) (fun b => g (f b))).toList := by
  simp [toList_mapM_eq_toList_filterMapM]

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
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [List.filterMap_cons, bind_assoc, pure_bind]
    split
    · split
      · simp only [bind_pure_comp, pure_bind, Shrink.inflate_deflate]
        exact ihy ‹_›
      · simp_all
    · split
      · simp_all
      · simp_all [ihy ‹_›]
  · simp only [bind_pure_comp, pure_bind, Shrink.inflate_deflate]
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

theorem IterM.toListRev_map_eq_toListRev_mapM {α β γ : Type w}
    {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {f : β → γ} {it : IterM (α := α) m β} :
    (it.map f).toListRev = (it.mapM fun b => pure (f b)).toListRev := by
  simp [toListRev_eq, toList_map_eq_toList_mapM]

theorem IterM.toListRev_mapM_eq_toListRev_filterMapM {α β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n][LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m] [IteratorCollect α m n] [LawfulIteratorCollect α m n]
    {f : β → n γ} {it : IterM (α := α) m β} :
    (it.mapM f).toListRev =
      (it.filterMapM fun b => some <$> f b).toListRev := by
  simp [toListRev_eq, toList_mapM_eq_toList_filterMapM]

theorem IterM.toListRev_map_eq_toListRev_filterMapM {α β γ : Type w}
    {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {f : β → γ} {it : IterM (α := α) m β} :
    (it.map f).toListRev = (it.filterMapM fun b => pure (some (f b))).toListRev := by
  simp [toListRev_eq, toList_map_eq_toList_filterMapM]

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

@[simp]
theorem IterM.toListRev_filterMapM_filterMapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m] [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {f : β → n (Option γ)} {g : γ → o (Option δ)}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.filterMapM f).filterMapM g).toListRev =
      (it.filterMapM (n := o) (fun b => do
        match ← f b with
        | none => return none
        | some fb => g fb)).toListRev := by
  simp [toListRev_eq]

@[simp]
theorem IterM.toListRev_filterMapM_mapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m] [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {f : β → n γ} {g : γ → o (Option δ)}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.mapM f).filterMapM g).toListRev =
      (it.filterMapM (n := o) (fun b => do g (← f b))).toListRev := by
  simp [toListRev_eq]

@[simp]
theorem IterM.toListRev_filterMapM_map {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m] [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {f : β → γ} {g : γ → n (Option δ)}
    {it : IterM (α := α) m β} :
    ((it.map f).filterMapM g).toListRev =
      (it.filterMapM (n := n) (fun b => g (f b))).toListRev := by
  simp [toListRev_eq]

@[simp]
theorem IterM.toListRev_mapM_filterMapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m] [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {f : β → n (Option γ)} {g : γ → o δ}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.filterMapM f).mapM g).toListRev =
      (it.filterMapM (n := o) (fun b => do
        match ← f b with
        | none => return none
        | some fb => some <$> g fb)).toListRev := by
  simp [toListRev_eq]

@[simp]
theorem IterM.toListRev_mapM_mapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m]
    {f : β → n γ} {g : γ → o δ}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.mapM f).mapM g).toListRev =
      (it.mapM (n := o) (fun b => do g (← f b))).toListRev := by
  letI : IteratorCollect α m o := .defaultImplementation
  simp [toListRev_eq]

@[simp]
theorem IterM.toListRev_mapM_map {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m] {f : β → γ} {g : γ → n δ} {it : IterM (α := α) m β} :
    ((it.map f).mapM g).toListRev =
      (it.mapM (n := n) (fun b => g (f b))).toListRev := by
  letI : IteratorCollect α m n := .defaultImplementation
  simp [toListRev_eq]

end ToListRev

section ToArray

theorem IterM.toArray_map_eq_toArray_mapM {α β γ : Type w}
    {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {f : β → γ} {it : IterM (α := α) m β} :
    (it.map f).toArray = (it.mapM fun b => pure (f b)).toArray := by
  simp [← toArray_toList, toList_map_eq_toList_mapM]

theorem IterM.toArray_mapM_eq_toArray_filterMapM {α β γ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n][LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m] [IteratorCollect α m n] [LawfulIteratorCollect α m n]
    {f : β → n γ} {it : IterM (α := α) m β} :
    (it.mapM f).toArray = (it.filterMapM fun b => some <$> f b).toArray := by
  simp [← toArray_toList, toList_mapM_eq_toList_filterMapM]

theorem IterM.toArray_map_eq_toArray_filterMapM {α β γ : Type w}
    {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {f : β → γ} {it : IterM (α := α) m β} :
    (it.map f).toArray = (it.filterMapM fun b => pure (some (f b))).toArray := by
  simp [← toArray_toList, toList_map_eq_toList_filterMapM]

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

@[simp]
theorem IterM.toArray_filterMapM_filterMapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m] [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {f : β → n (Option γ)} {g : γ → o (Option δ)}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.filterMapM f).filterMapM g).toArray =
      (it.filterMapM (n := o) (fun b => do
        match ← f b with
        | none => return none
        | some fb => g fb)).toArray := by
  simp [← toArray_toList]

@[simp]
theorem IterM.toArray_filterMapM_mapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m] [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {f : β → n γ} {g : γ → o (Option δ)}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.mapM f).filterMapM g).toArray =
      (it.filterMapM (n := o) (fun b => do g (← f b))).toArray := by
  simp [← toArray_toList]

@[simp]
theorem IterM.toArray_filterMapM_map {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m] [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {f : β → γ} {g : γ → n (Option δ)}
    {it : IterM (α := α) m β} :
    ((it.map f).filterMapM g).toArray =
      (it.filterMapM (n := n) (fun b => g (f b))).toArray := by
  simp [← toArray_toList]

@[simp]
theorem IterM.toArray_mapM_filterMapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m] [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {f : β → n (Option γ)} {g : γ → o δ}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.filterMapM f).mapM g).toArray =
      (it.filterMapM (n := o) (fun b => do
        match ← f b with
        | none => return none
        | some fb => some <$> g fb)).toArray := by
  simp [← toArray_toList]

@[simp]
theorem IterM.toArray_mapM_mapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    [Iterator α m β] [Finite α m] [IteratorCollect α m o] [LawfulIteratorCollect α m o]
    {f : β → n γ} {g : γ → o δ}
    {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨monadLift⟩
    ((it.mapM f).mapM g).toArray =
      (it.mapM (n := o) (fun b => do g (← f b))).toArray := by
  simp [← toArray_toList]

@[simp]
theorem IterM.toArray_mapM_map {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Iterator α m β] [Finite α m] [IteratorCollect α m n] [LawfulIteratorCollect α m n]
    {f : β → γ} {g : γ → n δ}
    {it : IterM (α := α) m β} :
    ((it.map f).mapM g).toArray =
      (it.mapM (n := n) (fun b => g (f b))).toArray := by
  simp [← toArray_toList]

end ToArray

section Fold

theorem IterM.foldM_filterMapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α m β] [Finite α m]
    [Monad m] [Monad n] [Monad o] [LawfulMonad m] [LawfulMonad n] [LawfulMonad o]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → n (Option γ)} {g : δ → γ → o δ} {init : δ} {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
    (it.filterMapM f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do
          let some c ← f b | pure d
          g d c) := by
  letI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
  induction it using IterM.inductSteps generalizing init with | step it ihy ihs
  rw [foldM_eq_match_step, foldM_eq_match_step, step_filterMapM, liftM_bind, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [PlausibleIterStep.skip, PlausibleIterStep.yield, liftM_bind, bind_assoc]
    apply bind_congr; intro c?
    split <;> simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

theorem IterM.foldM_mapM {α β γ δ : Type w}
    {m : Type w → Type w'} {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α m β] [Finite α m]
    [Monad m] [Monad n] [Monad o] [LawfulMonad m] [LawfulMonad n] [LawfulMonad o]
    [IteratorLoop α m n] [IteratorLoop α m o]
    [LawfulIteratorLoop α m n] [LawfulIteratorLoop α m o]
    [MonadLiftT m n] [MonadLiftT n o] [LawfulMonadLiftT m n] [LawfulMonadLiftT n o]
    {f : β → n γ} {g : δ → γ → o δ} {init : δ} {it : IterM (α := α) m β} :
    haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
    (it.mapM f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do let c ← f b; g d c) := by
  letI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
  induction it using IterM.inductSteps generalizing init with | step it ihy ihs
  rw [foldM_eq_match_step, foldM_eq_match_step, step_mapM, liftM_bind, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

theorem IterM.foldM_filterMap {α β γ δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    [IteratorLoop α m m] [IteratorLoop α m n]
    [LawfulIteratorLoop α m m] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → Option γ} {g : δ → γ → n δ} {init : δ} {it : IterM (α := α) m β} :
    (it.filterMap f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do
          let some c := f b | pure d
          g d c) := by
  induction it using IterM.inductSteps generalizing init with | step it ihy ihs
  rw [foldM_eq_match_step, foldM_eq_match_step, step_filterMap, liftM_bind, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [PlausibleIterStep.skip, PlausibleIterStep.yield]
    split <;> simp [ihy ‹_›, *]
  · simp [ihs ‹_›]
  · simp

theorem IterM.foldM_map {α β γ δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    [IteratorLoop α m m] [IteratorLoop α m n]
    [LawfulIteratorLoop α m m] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → γ} {g : δ → γ → n δ} {init : δ} {it : IterM (α := α) m β} :
    (it.map f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do g d (f b)) := by
  induction it using IterM.inductSteps generalizing init with | step it ihy ihs
  rw [foldM_eq_match_step, foldM_eq_match_step, step_map, liftM_bind, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

theorem IterM.fold_filterMapM {α β γ δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    [IteratorLoop α m m] [IteratorLoop α m n]
    [LawfulIteratorLoop α m m] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → n (Option γ)} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β} :
    (it.filterMapM f).fold (init := init) g =
      it.foldM (init := init) (fun d b => do
          let some c ← f b | pure d
          return g d c) := by
  simp [fold_eq_foldM, foldM_filterMapM]

theorem IterM.fold_mapM {α β γ δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    [IteratorLoop α m m] [IteratorLoop α m n]
    [LawfulIteratorLoop α m m] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → n γ} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β} :
    (it.mapM f).fold (init := init) g =
      it.foldM (init := init) (fun d b => do let c ← f b; return g d c) := by
  simp [fold_eq_foldM, foldM_mapM]

theorem IterM.fold_filterMap {α β γ δ : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m] [LawfulMonad m]
    [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {f : β → Option γ} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β} :
    (it.filterMap f).fold (init := init) g =
      it.fold (init := init) (fun d b =>
          match f b with
          | some c => g d c
          | _ => d) := by
  simp [fold_eq_foldM, foldM_filterMap]
  congr; ext
  split <;> simp

theorem IterM.fold_map {α β γ δ : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m] [LawfulMonad m]
    [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {f : β → γ} {g : δ → γ → δ} {init : δ} {it : IterM (α := α) m β} :
    (it.map f).fold (init := init) g =
      it.fold (init := init) (fun d b => g d (f b)) := by
  simp [fold_eq_foldM, foldM_map]

end Fold

section AnyAll

theorem IterM.anyM_filterMapM {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [MonadLiftT m n]
    [LawfulMonad m] [LawfulMonad n]
    {it : IterM (α := α) m β} {f : β → n (Option β')} {p : β' → n (ULift Bool)} :
    (it.filterMapM f).anyM p = (it.mapM (pure (f := n))).anyM (fun x => do
      match ← f x with
      | some fx => p fx
      | none => return .up false) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [anyM_eq_match_step, anyM_eq_match_step, step_filterMapM, step_mapM, bind_assoc, bind_assoc]
  apply bind_congr; intro step
  split
  · simp only [bind_assoc, pure_bind, Shrink.inflate_deflate]
    apply bind_congr; intro fx
    split
    · simp [ihy ‹_›]
    · simp only [PlausibleIterStep.yield, pure_bind, Shrink.inflate_deflate]
      apply bind_congr; intro px
      split <;> simp [ihy ‹_›]
  · simp only [PlausibleIterStep.skip, pure_bind, bind_assoc]
    simp [ihs ‹_›]
  · simp

theorem IterM.anyM_mapM {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [MonadLiftT m n]
    [LawfulMonad m] [LawfulMonad n]
    {it : IterM (α := α) m β} {f : β → n β'} {p : β' → n (ULift Bool)} :
    (it.mapM f).anyM p = (it.mapM (pure (f := n))).anyM (fun x => do p (← f x)) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [anyM_eq_match_step, anyM_eq_match_step, step_mapM, step_mapM, bind_assoc, bind_assoc]
  apply bind_congr; intro step
  split
  · simp only [bind_assoc, pure_bind, Shrink.inflate_deflate]
    apply bind_congr; intro fx
    simp [ihy ‹_›]
  · simp only [PlausibleIterStep.skip, pure_bind, bind_assoc]
    simp [ihs ‹_›]
  · simp

theorem IterM.anyM_filterM {α β : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [MonadLiftT m n]
    [LawfulMonad m] [LawfulMonad n]
    {it : IterM (α := α) m β} {f : β → n (ULift Bool)} {p : β → n (ULift Bool)} :
    (it.filterM f).anyM p = (it.mapM (pure (f := n))).anyM (fun x => do
        if (← f x).down then
          p x
        else
          return .up false) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [anyM_eq_match_step, anyM_eq_match_step, step_mapM, step_filterM, bind_assoc, bind_assoc]
  apply bind_congr; intro step
  split
  · simp only [bind_assoc, pure_bind, Shrink.inflate_deflate]
    apply bind_congr; intro fx
    split <;> simp [ihy ‹_›]
  · simp only [PlausibleIterStep.skip, pure_bind, bind_assoc]
    simp [ihs ‹_›]
  · simp

theorem IterM.anyM_filterMap {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → Option β'} {p : β' → m (ULift Bool)} :
    (it.filterMap f).anyM p = it.anyM (fun x => do
      match f x with
      | some fx => p fx
      | none => return .up false) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [anyM_eq_match_step, anyM_eq_match_step, step_filterMap, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only
    split
    · simp [*, ihy ‹_›]
    · simp only [*, PlausibleIterStep.yield, pure_bind, Shrink.inflate_deflate]
      apply bind_congr; intro px
      split <;> simp [ihy ‹_›]
  · simp [PlausibleIterStep.skip, pure_bind, ihs ‹_›]
  · simp

theorem IterM.anyM_map {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → β'} {p : β' → m (ULift Bool)} :
    (it.map f).anyM p = it.anyM (fun x => p (f x)) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [anyM_eq_match_step, anyM_eq_match_step, step_map, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [pure_bind, Shrink.inflate_deflate]
    apply bind_congr; intro fx
    simp [ihy ‹_›]
  · simp [PlausibleIterStep.skip, pure_bind, ihs ‹_›]
  · simp

theorem IterM.anyM_filter {α β : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m][IteratorLoop α m m]
    [LawfulMonad m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → Bool} {p : β → m (ULift Bool)} :
    (it.filter f).anyM p = it.anyM (fun x => do
        if f x then
          p x
        else
          return .up false) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [anyM_eq_match_step, anyM_eq_match_step, step_filter, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only
    split <;> simp [ihy ‹_›]
  · simp only [PlausibleIterStep.skip, pure_bind]
    simp [ihs ‹_›]
  · simp

theorem IterM.any_filterMapM {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [MonadLiftT m n] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulMonad n] [LawfulMonadLiftT m n] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → n (Option β')} {p : β' → Bool} :
    (it.filterMapM f).any p = (it.mapM (pure (f := n))).anyM (fun x => do
      match ← f x with
      | some fx => return .up (p fx)
      | none => return .up false) := by
  simp [any_eq_anyM, anyM_filterMapM]

theorem IterM.any_mapM {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [MonadLiftT m n] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulMonad n] [LawfulMonadLiftT m n] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → n β'} {p : β' → Bool} :
    (it.mapM f).any p = (it.mapM (pure (f := n))).anyM (fun x => (.up <| p ·) <$> (f x)) := by
  simp [any_eq_anyM, anyM_mapM]

theorem IterM.any_filterM {α β : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [MonadLiftT m n] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulMonad n] [LawfulMonadLiftT m n] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → n (ULift Bool)} {p : β → Bool} :
    (it.filterM f).any p = (it.mapM (pure (f := n))).anyM (fun x => do
        if (← f x).down then
          return .up (p x)
        else
          return .up false) := by
  simp [any_eq_anyM, anyM_filterM]

theorem IterM.any_filterMap {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → Option β'} {p : β' → Bool} :
    (it.filterMap f).any p = it.any (fun x =>
      match f x with
      | some fx => (p fx)
      | none => false) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [any_eq_match_step, any_eq_match_step, step_filterMap, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only
    split
    · simp [*, ihy ‹_›]
    · simp only [*, PlausibleIterStep.yield, pure_bind, Shrink.inflate_deflate]
      split <;> simp [ihy ‹_›]
  · simp [PlausibleIterStep.skip, pure_bind, ihs ‹_›]
  · simp

theorem IterM.any_map {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → β'} {p : β' → Bool} :
    (it.map f).any p = it.any (fun x => p (f x)) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [any_eq_match_step, any_eq_match_step, step_map, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [pure_bind]
    simp [ihy ‹_›]
  · simp [PlausibleIterStep.skip, pure_bind, ihs ‹_›]
  · simp

theorem IterM.allM_filterMapM {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [MonadLiftT m n]
    [LawfulMonad m] [LawfulMonad n] [LawfulMonadLiftT m n]
    {it : IterM (α := α) m β} {f : β → n (Option β')} {p : β' → n (ULift Bool)} :
    (it.filterMapM f).allM p = (it.mapM (pure (f := n))).allM (fun x => do
      match ← f x with
      | some fx => p fx
      | none => return .up true) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [allM_eq_match_step, allM_eq_match_step, step_filterMapM, step_mapM, bind_assoc, bind_assoc]
  apply bind_congr; intro step
  split
  · simp only [bind_assoc, pure_bind, Shrink.inflate_deflate]
    apply bind_congr; intro fx
    split
    · simp [ihy ‹_›]
    · simp only [PlausibleIterStep.yield, pure_bind, Shrink.inflate_deflate]
      apply bind_congr; intro px
      split <;> simp [ihy ‹_›]
  · simp only [PlausibleIterStep.skip, pure_bind, bind_assoc]
    simp [ihs ‹_›]
  · simp

theorem IterM.allM_mapM {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [MonadLiftT m n]
    [LawfulMonad m] [LawfulMonad n] [LawfulMonadLiftT m n]
    {it : IterM (α := α) m β} {f : β → n β'} {p : β' → n (ULift Bool)} :
    (it.mapM f).allM p = (it.mapM (pure (f := n))).allM (fun x => do p (← f x)) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [allM_eq_match_step, allM_eq_match_step, step_mapM, step_mapM, bind_assoc, bind_assoc]
  apply bind_congr; intro step
  split
  · simp only [bind_assoc, pure_bind, Shrink.inflate_deflate]
    apply bind_congr; intro fx
    simp [ihy ‹_›]
  · simp only [PlausibleIterStep.skip, pure_bind, bind_assoc]
    simp [ihs ‹_›]
  · simp

theorem IterM.allM_filterM {α β : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [MonadLiftT m n]
    [LawfulMonad m] [LawfulMonad n] [LawfulMonadLiftT m n]
    {it : IterM (α := α) m β} {f : β → n (ULift Bool)} {p : β → n (ULift Bool)} :
    (it.filterM f).allM p = (it.mapM (pure (f := n))).allM (fun x => do
        if (← f x).down then
          p x
        else
          return .up true) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [allM_eq_match_step, allM_eq_match_step, step_mapM, step_filterM, bind_assoc, bind_assoc]
  apply bind_congr; intro step
  split
  · simp only [bind_assoc, pure_bind, Shrink.inflate_deflate]
    apply bind_congr; intro fx
    split <;> simp [ihy ‹_›]
  · simp only [PlausibleIterStep.skip, pure_bind, bind_assoc]
    simp [ihs ‹_›]
  · simp

theorem IterM.allM_filterMap {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → Option β'} {p : β' → m (ULift Bool)} :
    (it.filterMap f).allM p = it.allM (fun x => do
      match f x with
      | some fx => p fx
      | none => return .up true) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [allM_eq_match_step, allM_eq_match_step, step_filterMap, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only
    split
    · simp [*, ihy ‹_›]
    · simp only [*, PlausibleIterStep.yield, pure_bind, Shrink.inflate_deflate]
      apply bind_congr; intro px
      split <;> simp [ihy ‹_›]
  · simp [PlausibleIterStep.skip, pure_bind, ihs ‹_›]
  · simp

theorem IterM.allM_map {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → β'} {p : β' → m (ULift Bool)} :
    (it.map f).allM p = it.allM (fun x => p (f x)) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [allM_eq_match_step, allM_eq_match_step, step_map, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [pure_bind, Shrink.inflate_deflate]
    apply bind_congr; intro fx
    simp [ihy ‹_›]
  · simp [PlausibleIterStep.skip, pure_bind, ihs ‹_›]
  · simp

theorem IterM.allM_filter {α β : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m][IteratorLoop α m m]
    [LawfulMonad m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → Bool} {p : β → m (ULift Bool)} :
    (it.filter f).allM p = it.allM (fun x => do
        if f x then
          p x
        else
          return .up true) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [allM_eq_match_step, allM_eq_match_step, step_filter, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only
    split <;> simp [ihy ‹_›]
  · simp only [PlausibleIterStep.skip, pure_bind]
    simp [ihs ‹_›]
  · simp

theorem IterM.all_filterMapM {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [MonadLiftT m n] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulMonad n] [LawfulMonadLiftT m n] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → n (Option β')} {p : β' → Bool} :
    (it.filterMapM f).all p = (it.mapM (pure (f := n))).allM (fun x => do
      match ← f x with
      | some fx => return .up (p fx)
      | none => return .up true) := by
  simp [all_eq_allM, allM_filterMapM]

theorem IterM.all_mapM {α β β' : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [MonadLiftT m n] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulMonad n] [LawfulMonadLiftT m n] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → n β'} {p : β' → Bool} :
    (it.mapM f).all p = (it.mapM (pure (f := n))).allM (fun x => (.up <| p ·) <$> (f x)) := by
  simp [all_eq_allM, allM_mapM]

theorem IterM.all_filterM {α β : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α m β] [Finite α m] [Monad m] [Monad n] [MonadLiftT m n] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulMonad n] [LawfulMonadLiftT m n] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → n (ULift Bool)} {p : β → Bool} :
    (it.filterM f).all p = (it.mapM (pure (f := n))).allM (fun x => do
        if (← f x).down then
          return .up (p x)
        else
          return .up true) := by
  simp [all_eq_allM, allM_filterM]

theorem IterM.all_filterMap {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → Option β'} {p : β' → Bool} :
    (it.filterMap f).all p = it.all (fun x =>
      match f x with
      | some fx => (p fx)
      | none => true) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [all_eq_match_step, all_eq_match_step, step_filterMap, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only
    split
    · simp [*, ihy ‹_›]
    · simp only [*, PlausibleIterStep.yield, pure_bind, Shrink.inflate_deflate]
      split <;> simp [ihy ‹_›]
  · simp [PlausibleIterStep.skip, pure_bind, ihs ‹_›]
  · simp

theorem IterM.all_map {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α m β] [Finite α m] [Monad m] [IteratorLoop α m m]
    [LawfulMonad m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} {f : β → β'} {p : β' → Bool} :
    (it.map f).all p = it.all (fun x => p (f x)) := by
  induction it using IterM.inductSteps with | step it ihy ihs
  rw [all_eq_match_step, all_eq_match_step, step_map, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [pure_bind]
    simp [ihy ‹_›]
  · simp [PlausibleIterStep.skip, pure_bind, ihs ‹_›]
  · simp

end AnyAll

end Std.Iterators
