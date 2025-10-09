/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Lemmas.Consumers
public import Init.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap
public import Init.Data.Iterators.Combinators.FilterMap

public section

namespace Std.Iterators

variable {α β γ : Type w} [Iterator α Id β] {it : Iter (α := α) β}
    {m : Type w → Type w'} {n : Type w → Type w''}

theorem Iter.filterMapWithPostcondition_eq_toIter_filterMapWithPostcondition_toIterM [Monad m]
    {f : β → PostconditionT m (Option γ)} :
    it.filterMapWithPostcondition f = (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.filterMapWithPostcondition f) :=
  rfl

theorem Iter.filterWithPostcondition_eq_toIter_filterMapWithPostcondition_toIterM [Monad m]
    {f : β → PostconditionT m (ULift Bool)} :
    it.filterWithPostcondition f = (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.filterWithPostcondition f) :=
  rfl

theorem Iter.mapWithPostcondition_eq_toIter_mapWithPostcondition_toIterM [Monad m] {f : β → PostconditionT m γ} :
    it.mapWithPostcondition f = (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.mapWithPostcondition f) :=
  rfl

theorem Iter.filterMapM_eq_toIter_filterMapM_toIterM [Monad m] {f : β → m (Option γ)} :
    it.filterMapM f = (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.filterMapM f) :=
  rfl

theorem Iter.filterM_eq_toIter_filterM_toIterM [Monad m] {f : β → m (ULift Bool)} :
    it.filterM f = (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.filterM f) :=
  rfl

theorem Iter.mapM_eq_toIter_mapM_toIterM [Monad m] {f : β → m γ} :
    it.mapM f = (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.mapM f) :=
  rfl

theorem Iter.filterMap_eq_toIter_filterMap_toIterM {f : β → Option γ} :
    it.filterMap f = (it.toIterM.filterMap f).toIter :=
  rfl

theorem Iter.map_eq_toIter_map_toIterM {f : β → γ} :
    it.map f = (it.toIterM.map f).toIter :=
  rfl

theorem Iter.filter_eq_toIter_filter_toIterM [Monad m] {f : β → Bool} :
    it.filter f = (it.toIterM.filter f).toIter :=
  rfl

theorem Iter.step_filterMapWithPostcondition {f : β → PostconditionT n (Option γ)}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.filterMapWithPostcondition f).step = (do
    match it.step with
    | .yield it' out h => do
      match ← (f out).operation with
      | ⟨none, h'⟩ =>
        pure <| .deflate <| .skip (it'.filterMapWithPostcondition f) (.yieldNone (out := out) h h')
      | ⟨some out', h'⟩ =>
        pure <| .deflate <| .yield (it'.filterMapWithPostcondition f) out' (.yieldSome (out := out) h h')
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.filterMapWithPostcondition f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (.done h)) := by
  simp only [filterMapWithPostcondition_eq_toIter_filterMapWithPostcondition_toIterM, IterM.step_filterMapWithPostcondition,
    step]
  simp only [liftM, monadLift, pure_bind]
  generalize it.toIterM.step = step
  match step.inflate with
  | .yield it' out h =>
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem Iter.step_filterWithPostcondition {f : β → PostconditionT n (ULift Bool)}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.filterWithPostcondition f).step = (do
    match it.step with
    | .yield it' out h => do
      match ← (f out).operation with
      | ⟨.up false, h'⟩ =>
        pure <| .deflate <| .skip (it'.filterWithPostcondition f) (.yieldNone (out := out) h ⟨⟨_, h'⟩, rfl⟩)
      | ⟨.up true, h'⟩ =>
        pure <| .deflate <| .yield (it'.filterWithPostcondition f) out (.yieldSome (out := out) h ⟨⟨_, h'⟩, rfl⟩)
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.filterWithPostcondition f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (.done h)) := by
  simp only [filterWithPostcondition_eq_toIter_filterMapWithPostcondition_toIterM, IterM.step_filterWithPostcondition, step]
  simp only [liftM, monadLift, pure_bind]
  generalize it.toIterM.step = step
  match step.inflate with
  | .yield it' out h =>
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem Iter.step_mapWithPostcondition {f : β → PostconditionT n γ}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.mapWithPostcondition f).step = (do
    match it.step with
    | .yield it' out h => do
      let out' ← (f out).operation
      pure <| .deflate <| .yield (it'.mapWithPostcondition f) out'.1 (.yieldSome h ⟨out', rfl⟩)
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.mapWithPostcondition f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (.done h)) := by
  simp only [mapWithPostcondition_eq_toIter_mapWithPostcondition_toIterM, IterM.step_mapWithPostcondition, step]
  simp only [liftM, monadLift, pure_bind]
  generalize it.toIterM.step = step
  match step.inflate with
  | .yield it' out h =>
    simp only [bind_pure_comp]
    rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem Iter.step_filterMapM {β' : Type w} {f : β → n (Option β')}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.filterMapM f).step = (do
    match it.step with
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
  simp only [filterMapM_eq_toIter_filterMapM_toIterM, IterM.step_filterMapM, step]
  simp only [liftM, monadLift, pure_bind]
  generalize it.toIterM.step = step
  match step.inflate with
  | .yield it' out h =>
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem Iter.step_filterM {f : β → n (ULift Bool)}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.filterM f).step = (do
    match it.step with
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
  simp only [filterM_eq_toIter_filterM_toIterM, IterM.step_filterM, step]
  simp only [liftM, monadLift, pure_bind]
  generalize it.toIterM.step = step
  match step.inflate with
  | .yield it' out h =>
    simp [PostconditionT.lift]
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem Iter.step_mapM {f : β → n γ}
    [Monad n] [LawfulMonad n] :
  (it.mapM f).step = (do
    match it.step with
    | .yield it' out h => do
      let out' ← f out
      pure <| .deflate <| .yield (it'.mapM f) out' (.yieldSome h ⟨⟨out', True.intro⟩, rfl⟩)
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.mapM f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (.done h)) := by
  simp only [mapM_eq_toIter_mapM_toIterM, IterM.step_mapM, step]
  simp only [liftM, monadLift, pure_bind]
  generalize it.toIterM.step = step
  match step.inflate with
  | .yield it' out h =>
    simp only [bind_pure_comp]
    rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem Iter.step_filterMap {f : β → Option γ} :
    (it.filterMap f).step = match it.step with
      | .yield it' out h =>
        match h' : f out with
        | none => .skip (it'.filterMap f) (.yieldNone (out := out) h h')
        | some out' => .yield (it'.filterMap f) out' (.yieldSome (out := out) h h')
      | .skip it' h => .skip (it'.filterMap f) (.skip h)
      | .done h => .done (.done h) := by
  simp only [filterMap_eq_toIter_filterMap_toIterM, toIterM_toIter, IterM.step_filterMap, step]
  simp only [monadLift, Id.run_bind]
  generalize it.toIterM.step.run = step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only [IterM.Step.toPure_yield, toIter_toIterM, toIterM_toIter]
    split <;> split <;> (try exfalso; simp_all; done)
    · simp
    · rename_i h₁ _ h₂
      rw [h₁] at h₂
      cases h₂
      simp
  · simp
  · simp

/--
a weaker version of `step_filterMap` that does not use dependent `match`
-/
theorem Iter.val_step_filterMap {f : β → Option γ} :
    (it.filterMap f).step.val = match it.step.val with
      | .yield it' out =>
        match f out with
        | none => .skip (it'.filterMap f)
        | some out' => .yield (it'.filterMap f) out'
      | .skip it' => .skip (it'.filterMap f)
      | .done => .done := by
  simp [step_filterMap]
  cases it.step using PlausibleIterStep.casesOn
  · simp only
    split <;> simp_all
  · simp
  · simp

theorem Iter.step_map {f : β → γ} :
    (it.map f).step = match it.step with
      | .yield it' out h =>
        .yield (it'.map f) (f out) (.yieldSome (out := out) h ⟨⟨f out, rfl⟩, rfl⟩)
      | .skip it' h =>
        .skip (it'.map f) (.skip h)
      | .done h =>
        .done (.done h) := by
  simp only [map_eq_toIter_map_toIterM, step, toIterM_toIter, IterM.step_map, Id.run_bind]
  generalize it.toIterM.step.run = step
  cases step.inflate using PlausibleIterStep.casesOn <;> simp

def Iter.step_filter {f : β → Bool} :
    (it.filter f).step = match it.step with
      | .yield it' out h =>
        if h' : f out = true then
          .yield (it'.filter f) out (.yieldSome (out := out) h (by simp [h']))
        else
          .skip (it'.filter f) (.yieldNone h (by simp [h']))
      | .skip it' h =>
        .skip (it'.filter f) (.skip h)
      | .done h =>
        .done (.done h) := by
  simp only [filter_eq_toIter_filter_toIterM, step, toIterM_toIter, IterM.step_filter, Id.run_bind]
  generalize it.toIterM.step.run = step
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only
    split <;> simp [*]
  · simp
  · simp

def Iter.val_step_filter {f : β → Bool} :
    (it.filter f).step.val = match it.step.val with
      | .yield it' out =>
        if f out = true then
          .yield (it'.filter f) out
        else
          .skip (it'.filter f)
      | .skip it' =>
        .skip (it'.filter f)
      | .done =>
        .done := by
  simp only [filter_eq_toIter_filter_toIterM, step, toIterM_toIter, IterM.step_filter, Id.run_bind]
  generalize it.toIterM.step.run = step
  cases step using PlausibleIterStep.casesOn
  · simp only
    split <;> simp [*]
  · simp
  · simp

@[simp]
theorem Iter.toList_filterMap
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id] [Finite α Id]
    {f : β → Option γ} :
    (it.filterMap f).toList = it.toList.filterMap f := by
  simp [filterMap_eq_toIter_filterMap_toIterM, toList_eq_toList_toIterM, IterM.toList_filterMap]

@[simp]
theorem Iter.toList_map
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id] [Finite α Id]
    {f : β → γ} :
    (it.map f).toList = it.toList.map f := by
  simp [map_eq_toIter_map_toIterM, IterM.toList_map, Iter.toList_eq_toList_toIterM]

@[simp]
theorem Iter.toList_filter
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id] [Finite α Id]
    {f : β → Bool} :
    (it.filter f).toList = it.toList.filter f := by
  simp [filter_eq_toIter_filter_toIterM, IterM.toList_filter, Iter.toList_eq_toList_toIterM]

@[simp]
theorem Iter.toListRev_filterMap
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id] [Finite α Id]
    {f : β → Option γ} :
    (it.filterMap f).toListRev = it.toListRev.filterMap f := by
  simp [filterMap_eq_toIter_filterMap_toIterM, toListRev_eq_toListRev_toIterM, IterM.toListRev_filterMap]

@[simp]
theorem Iter.toListRev_map
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id] [Finite α Id]
    {f : β → γ} :
    (it.map f).toListRev = it.toListRev.map f := by
  simp [map_eq_toIter_map_toIterM, IterM.toListRev_map, Iter.toListRev_eq_toListRev_toIterM]

@[simp]
theorem Iter.toListRev_filter
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id] [Finite α Id]
    {f : β → Bool} :
    (it.filter f).toListRev = it.toListRev.filter f := by
  simp [filter_eq_toIter_filter_toIterM, IterM.toListRev_filter, Iter.toListRev_eq_toListRev_toIterM]

@[simp]
theorem Iter.toArray_filterMap
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id] [Finite α Id]
    {f : β → Option γ} :
    (it.filterMap f).toArray = it.toArray.filterMap f := by
  simp [filterMap_eq_toIter_filterMap_toIterM, toArray_eq_toArray_toIterM, IterM.toArray_filterMap]

@[simp]
theorem Iter.toArray_map
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id] [Finite α Id]
    {f : β → γ} :
    (it.map f).toArray = it.toArray.map f := by
  simp [map_eq_toIter_map_toIterM, IterM.toArray_map, Iter.toArray_eq_toArray_toIterM]

@[simp]
theorem Iter.toArray_filter
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id] [Finite α Id]
    {f : β → Bool} :
    (it.filter f).toArray = it.toArray.filter f := by
  simp [filter_eq_toIter_filter_toIterM, IterM.toArray_filter, Iter.toArray_eq_toArray_toIterM]

section Fold

theorem Iter.foldM_filterMapM {α β γ δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α Id β] [Finite α Id] [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    [IteratorLoop α Id Id] [IteratorLoop α Id m] [IteratorLoop α Id n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    [LawfulIteratorLoop α Id Id] [LawfulIteratorLoop α Id m] [LawfulIteratorLoop α Id n]
    {f : β → m (Option γ)} {g : δ → γ → n δ} {init : δ} {it : Iter (α := α) β} :
    (it.filterMapM f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do
          let some c ← f b | pure d
          g d c) := by
  rw [foldM_eq_foldM_toIterM, filterMapM_eq_toIter_filterMapM_toIterM, IterM.foldM_filterMapM]
  congr
  simp [instMonadLiftTOfMonadLift, Id.instMonadLiftTOfPure]

theorem Iter.foldM_mapM {α β γ δ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
    [Iterator α Id β] [Finite α Id] [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    [IteratorLoop α Id m] [IteratorLoop α Id n]
    [LawfulIteratorLoop α Id m] [LawfulIteratorLoop α Id n]
    [MonadLiftT m n] [LawfulMonadLiftT m n]
    {f : β → m γ} {g : δ → γ → n δ} {init : δ} {it : Iter (α := α) β} :
    (it.mapM f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do let c ← f b; g d c) := by
  rw [foldM_eq_foldM_toIterM, mapM_eq_toIter_mapM_toIterM, IterM.foldM_mapM]
  congr
  simp [instMonadLiftTOfMonadLift, Id.instMonadLiftTOfPure]

theorem Iter.foldM_filterMap {α β γ : Type w} {δ : Type x} {m : Type x → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
    [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {f : β → Option γ} {g : δ → γ → m δ} {init : δ} {it : Iter (α := α) β} :
    (it.filterMap f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do
          let some c := f b | pure d
          g d c) := by
  induction it using Iter.inductSteps generalizing init with | step it ihy ihs
  rw [foldM_eq_match_step, foldM_eq_match_step, step_filterMap]
  -- There seem to be some type dependencies that, combined with nested match expressions,
  -- force us to split a lot.
  split <;> rename_i h
  · split at h
    · split at h
      · cases h
      · cases h; simp [*, ihy ‹_›]
    · cases h
    · cases h
  · split at h
    · split at h
      · cases h; simp [*, ihy ‹_›]
      · cases h
    · cases h; simp [*, ihs ‹_›]
    · cases h
  · split at h
    · split at h
      · cases h
      · cases h
    · cases h
    · simp [*]

theorem Iter.foldM_map {α β γ : Type w} {δ : Type x} {m : Type x → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
    [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {f : β → γ} {g : δ → γ → m δ} {init : δ} {it : Iter (α := α) β} :
    (it.map f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => g d (f b)) := by
  induction it using Iter.inductSteps generalizing init with | step it ihy ihs
  rw [foldM_eq_match_step, foldM_eq_match_step, step_map]
  cases it.step using PlausibleIterStep.casesOn
  · simp [*, ihy ‹_›]
  · simp [*, ihs ‹_›]
  · simp

theorem Iter.fold_filterMapM {α β γ δ : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
    [IteratorLoop α Id Id.{w}] [IteratorLoop α Id m]
    [LawfulIteratorLoop α Id Id] [LawfulIteratorLoop α Id m]
    {f : β → m (Option γ)} {g : δ → γ → δ} {init : δ} {it : Iter (α := α) β} :
    (it.filterMapM f).fold (init := init) g =
      it.foldM (init := init) (fun d b => do
          let some c ← f b | pure d
          return g d c) := by
  rw [foldM_eq_foldM_toIterM, filterMapM_eq_toIter_filterMapM_toIterM, IterM.fold_filterMapM]
  rfl

theorem Iter.fold_mapM {α β γ δ : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
    [IteratorLoop α Id Id.{w}] [IteratorLoop α Id m]
    [LawfulIteratorLoop α Id Id] [LawfulIteratorLoop α Id m]
    {f : β → m γ} {g : δ → γ → δ} {init : δ} {it : Iter (α := α) β} :
    (it.mapM f).fold (init := init) g =
      it.foldM (init := init) (fun d b => do return g d (← f b)) := by
  rw [foldM_eq_foldM_toIterM, mapM_eq_toIter_mapM_toIterM, IterM.fold_mapM]

theorem Iter.fold_filterMap {α β γ : Type w} {δ : Type x}
    [Iterator α Id β] [Finite α Id] [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    {f : β → Option γ} {g : δ → γ → δ} {init : δ} {it : Iter (α := α) β} :
    (it.filterMap f).fold (init := init) g =
      it.fold (init := init) (fun d b =>
          match f b with
          | some c => g d c
          | _ => d) := by
  simp only [fold_eq_foldM, foldM_filterMap]
  rfl

theorem Iter.fold_map {α β γ : Type w} {δ : Type x}
    [Iterator α Id β] [Finite α Id]
    [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    {f : β → γ} {g : δ → γ → δ} {init : δ} {it : Iter (α := α) β} :
    (it.map f).fold (init := init) g =
      it.fold (init := init) (fun d b => g d (f b)) := by
  simp [fold_eq_foldM, foldM_map]

end Fold

theorem Iter.anyM_filterMapM {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
    {it : Iter (α := α) β} {f : β → m (Option β')} {p : β' → m (ULift Bool)} :
    (it.filterMapM f).anyM p = (it.mapM (pure (f := m))).anyM (fun x => do
      match ← f x with
      | some fx => p fx
      | none => return .up false) := by
  simp only [filterMapM_eq_toIter_filterMapM_toIterM, IterM.anyM_filterMapM]
  rfl

-- There is hope to generalize the following theorem as soon there is a `Shrink` type.
/--
This lemma expresses `Iter.anyM` in terms of `IterM.anyM`.
It requires all involved types to live in `Type 0`.
-/
theorem Iter.anyM_eq_anyM_mapM_pure {α β : Type} {m : Type → Type w'} [Iterator α Id β]
    [Finite α Id] [Monad m] [LawfulMonad m] [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {it : Iter (α := α) β} {p : β → m Bool} :
    it.anyM p = ULift.down <$> (it.mapM (α := α) (pure (f := m))).anyM (fun x => ULift.up <$> p x) := by
  rw [anyM_eq_forIn, IterM.anyM_eq_forIn, map_eq_pure_bind]
  induction it using Iter.inductSteps with | step it ihy ihs =>
  rw [forIn_eq_match_step, IterM.forIn_eq_match_step, bind_assoc, step_mapM]
  cases it.step using PlausibleIterStep.casesOn
  · simp only [bind_assoc, liftM_pure, pure_bind, map_eq_pure_bind]
    apply bind_congr; intro px
    split
    · simp
    · simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

theorem Iter.anyM_mapM {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
    {it : Iter (α := α) β} {f : β → m β'} {p : β' → m (ULift Bool)} :
    (it.mapM f).anyM p = (it.mapM (pure (f := m))).anyM (fun x => do p (← f x)) := by
  rw [mapM_eq_toIter_mapM_toIterM, IterM.anyM_mapM, mapM_eq_toIter_mapM_toIterM]

theorem Iter.anyM_filterM {α β : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
    {it : Iter (α := α) β} {f : β → m (ULift Bool)} {p : β → m (ULift Bool)} :
    (it.filterM f).anyM p = (it.mapM (pure (f := m))).anyM (fun x => do
        if (← f x).down then
          p x
        else
          return .up false) := by
  rw [filterM_eq_toIter_filterM_toIterM, IterM.anyM_filterM, mapM_eq_toIter_mapM_toIterM]

theorem Iter.anyM_filterMap {α β β' : Type w} {m : Type → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [IteratorLoop α Id m]
    [LawfulMonad m] [LawfulIteratorLoop α Id m]
    {it : Iter (α := α) β} {f : β → Option β'} {p : β' → m Bool} :
    (it.filterMap f).anyM p = it.anyM (fun x => do
      match f x with
      | some fx => p fx
      | none => return false) := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [anyM_eq_match_step, anyM_eq_match_step, val_step_filterMap]
  cases it.step using PlausibleIterStep.casesOn
  · rename_i out _
    simp only
    cases f out
    · simp [ihy ‹_›]
    · apply bind_congr; intro px
      split <;> simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

theorem Iter.anyM_map {α β β' : Type w} {m : Type → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [IteratorLoop α Id m]
    [LawfulMonad m] [LawfulIteratorLoop α Id m]
    {it : Iter (α := α) β} {f : β → β'} {p : β' → m Bool} :
    (it.map f).anyM p = it.anyM (fun x => p (f x)) := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [anyM_eq_match_step, anyM_eq_match_step, step_map]
  cases it.step using PlausibleIterStep.casesOn
  · simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

theorem Iter.anyM_filter {α β : Type w} {m : Type → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m][IteratorLoop α Id m]
    [LawfulMonad m] [LawfulIteratorLoop α Id m]
    {it : Iter (α := α) β} {f : β → Bool} {p : β → m Bool} :
    (it.filter f).anyM p = it.anyM (fun x => do
        if f x then
          p x
        else
          return false) := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [anyM_eq_match_step, anyM_eq_match_step, val_step_filter]
  cases it.step using PlausibleIterStep.casesOn
  · rename_i out _
    simp only
    cases f out <;> simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

theorem Iter.any_filterMapM {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [IteratorLoop α Id m]
    [LawfulMonad m] [LawfulIteratorLoop α Id m]
    {it : Iter (α := α) β} {f : β → m (Option β')} {p : β' → Bool} :
    (it.filterMapM f).any p = (it.mapM (pure (f := m))).anyM (fun x => do
      match ← f x with
      | some fx => return .up (p fx)
      | none => return .up false) := by
  simp [IterM.any_eq_anyM, anyM_filterMapM]

theorem Iter.any_mapM {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [IteratorLoop α Id m]
    [LawfulMonad m] [LawfulIteratorLoop α Id m]
    {it : Iter (α := α) β} {f : β → m β'} {p : β' → Bool} :
    (it.mapM f).any p = (it.mapM pure).anyM (fun x => (.up <| p ·) <$> (f x)) := by
  simp [IterM.any_eq_anyM, anyM_mapM]

theorem Iter.any_filterM {α β : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [IteratorLoop α Id m]
    [LawfulMonad m] [LawfulIteratorLoop α Id m]
    {it : Iter (α := α) β} {f : β → m (ULift Bool)} {p : β → Bool} :
    (it.filterM f).any p = (it.mapM (pure (f := m))).anyM (fun x => do
        if (← f x).down then
          return .up (p x)
        else
          return .up false) := by
  simp [IterM.any_eq_anyM, anyM_filterM]

theorem Iter.any_filterMap {α β β' : Type w}
    [Iterator α Id β] [Finite α Id][IteratorLoop α Id Id]
    [LawfulIteratorLoop α Id Id]
    {it : Iter (α := α) β} {f : β → Option β'} {p : β' → Bool} :
    (it.filterMap f).any p = it.any (fun x =>
      match f x with
      | some fx => (p fx)
      | none => false) := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [any_eq_match_step, any_eq_match_step, val_step_filterMap]
  cases it.step using PlausibleIterStep.casesOn
  · rename_i out _
    simp only
    cases f out
    · simp [*, ihy ‹_›]
    · simp only
      split <;> simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

theorem Iter.any_map {α β β' : Type w}
    [Iterator α Id β] [Finite α Id] [IteratorLoop α Id Id]
    [LawfulIteratorLoop α Id Id]
    {it : Iter (α := α) β} {f : β → β'} {p : β' → Bool} :
    (it.map f).any p = it.any (fun x => p (f x)) := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [any_eq_match_step, any_eq_match_step, step_map]
  cases it.step using PlausibleIterStep.casesOn
  · simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

theorem Iter.allM_filterMapM {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
    {it : Iter (α := α) β} {f : β → m (Option β')} {p : β' → m (ULift Bool)} :
    (it.filterMapM f).allM p = (it.mapM (pure (f := m))).allM (fun x => do
      match ← f x with
      | some fx => p fx
      | none => return .up true) := by
  simp only [filterMapM_eq_toIter_filterMapM_toIterM, IterM.allM_filterMapM]
  rfl

/--
This lemma expresses `Iter.allM` in terms of `IterM.allM`.
It requires all involved types to live in `Type 0`.
-/
theorem Iter.allM_eq_allM_mapM_pure {α β : Type} {m : Type → Type w'} [Iterator α Id β]
    [Finite α Id] [Monad m] [LawfulMonad m] [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {it : Iter (α := α) β} {p : β → m Bool} :
    it.allM p = ULift.down <$> (it.mapM (α := α) (pure (f := m))).allM (fun x => ULift.up <$> p x) := by
  rw [allM_eq_forIn, IterM.allM_eq_forIn, map_eq_pure_bind]
  induction it using Iter.inductSteps with | step it ihy ihs =>
  rw [forIn_eq_match_step, IterM.forIn_eq_match_step, bind_assoc, step_mapM]
  cases it.step using PlausibleIterStep.casesOn
  · simp only [bind_assoc, liftM_pure, pure_bind, map_eq_pure_bind]
    apply bind_congr; intro px
    split
    · simp [ihy ‹_›]
    · simp
  · simp [ihs ‹_›]
  · simp

theorem Iter.allM_mapM {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
    {it : Iter (α := α) β} {f : β → m β'} {p : β' → m (ULift Bool)} :
    (it.mapM f).allM p = (it.mapM (pure (f := m))).allM (fun x => do p (← f x)) := by
  rw [mapM_eq_toIter_mapM_toIterM, IterM.allM_mapM, mapM_eq_toIter_mapM_toIterM]

theorem Iter.allM_filterM {α β : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [LawfulMonad m]
    {it : Iter (α := α) β} {f : β → m (ULift Bool)} {p : β → m (ULift Bool)} :
    (it.filterM f).allM p = (it.mapM (pure (f := m))).allM (fun x => do
        if (← f x).down then
          p x
        else
          return .up true) := by
  rw [filterM_eq_toIter_filterM_toIterM, IterM.allM_filterM, mapM_eq_toIter_mapM_toIterM]

theorem Iter.allM_filterMap {α β β' : Type w} {m : Type → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [IteratorLoop α Id m]
    [LawfulMonad m] [LawfulIteratorLoop α Id m]
    {it : Iter (α := α) β} {f : β → Option β'} {p : β' → m Bool} :
    (it.filterMap f).allM p = it.allM (fun x => do
      match f x with
      | some fx => p fx
      | none => return true) := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [allM_eq_match_step, allM_eq_match_step, val_step_filterMap]
  cases it.step using PlausibleIterStep.casesOn
  · rename_i out _
    simp only
    cases f out
    · simp [ihy ‹_›]
    · apply bind_congr; intro px
      split <;> simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

theorem Iter.allM_map {α β β' : Type w} {m : Type → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [IteratorLoop α Id m]
    [LawfulMonad m] [LawfulIteratorLoop α Id m]
    {it : Iter (α := α) β} {f : β → β'} {p : β' → m Bool} :
    (it.map f).allM p = it.allM (fun x => p (f x)) := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [allM_eq_match_step, allM_eq_match_step, step_map]
  cases it.step using PlausibleIterStep.casesOn
  · simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

theorem Iter.allM_filter {α β : Type w} {m : Type → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m][IteratorLoop α Id m]
    [LawfulMonad m] [LawfulIteratorLoop α Id m]
    {it : Iter (α := α) β} {f : β → Bool} {p : β → m Bool} :
    (it.filter f).allM p = it.allM (fun x => do
        if f x then
          p x
        else
          return true) := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [allM_eq_match_step, allM_eq_match_step, val_step_filter]
  cases it.step using PlausibleIterStep.casesOn
  · rename_i out _
    simp only
    cases f out <;> simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

theorem Iter.all_filterMapM {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [IteratorLoop α Id m]
    [LawfulMonad m] [LawfulIteratorLoop α Id m]
    {it : Iter (α := α) β} {f : β → m (Option β')} {p : β' → Bool} :
    (it.filterMapM f).all p = (it.mapM (pure (f := m))).allM (fun x => do
      match ← f x with
      | some fx => return .up (p fx)
      | none => return .up true) := by
  simp [IterM.all_eq_allM, allM_filterMapM]

theorem Iter.all_mapM {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [IteratorLoop α Id m]
    [LawfulMonad m] [LawfulIteratorLoop α Id m]
    {it : Iter (α := α) β} {f : β → m β'} {p : β' → Bool} :
    (it.mapM f).all p = (it.mapM pure).allM (fun x => (.up <| p ·) <$> (f x)) := by
  simp [IterM.all_eq_allM, allM_mapM]

theorem Iter.all_filterM {α β : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [IteratorLoop α Id m]
    [LawfulMonad m] [LawfulIteratorLoop α Id m]
    {it : Iter (α := α) β} {f : β → m (ULift Bool)} {p : β → Bool} :
    (it.filterM f).all p = (it.mapM (pure (f := m))).allM (fun x => do
        if (← f x).down then
          return .up (p x)
        else
          return .up true) := by
  simp [IterM.all_eq_allM, allM_filterM]

theorem Iter.all_filterMap {α β β' : Type w}
    [Iterator α Id β] [Finite α Id][IteratorLoop α Id Id]
    [LawfulIteratorLoop α Id Id]
    {it : Iter (α := α) β} {f : β → Option β'} {p : β' → Bool} :
    (it.filterMap f).all p = it.all (fun x =>
      match f x with
      | some fx => (p fx)
      | none => true) := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [all_eq_match_step, all_eq_match_step, val_step_filterMap]
  cases it.step using PlausibleIterStep.casesOn
  · rename_i out _
    simp only
    cases f out
    · simp [*, ihy ‹_›]
    · simp only
      split <;> simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

theorem Iter.all_map {α β β' : Type w}
    [Iterator α Id β] [Finite α Id] [IteratorLoop α Id Id]
    [LawfulIteratorLoop α Id Id]
    {it : Iter (α := α) β} {f : β → β'} {p : β' → Bool} :
    (it.map f).all p = it.all (fun x => p (f x)) := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [all_eq_match_step, all_eq_match_step, step_map]
  cases it.step using PlausibleIterStep.casesOn
  · simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

end Std.Iterators
