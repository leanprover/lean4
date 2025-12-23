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
import Init.Control.Lawful.MonadAttach.Lemmas

public section

namespace Std
open Std.Iterators

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

theorem Iter.filterMapM_eq_toIter_filterMapM_toIterM [Monad m] [MonadAttach m] {f : β → m (Option γ)} :
    it.filterMapM f = (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.filterMapM f) :=
  rfl

theorem Iter.filterM_eq_toIter_filterM_toIterM [Monad m] [MonadAttach m] {f : β → m (ULift Bool)} :
    it.filterM f = (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.filterM f) :=
  rfl

theorem Iter.mapM_eq_toIter_mapM_toIterM [Monad m] [MonadAttach m] {f : β → m γ} :
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
    [Monad n] [LawfulMonad n] :
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
    [Monad n] [MonadAttach n] [LawfulMonad n] [MonadLiftT m n] :
  (it.filterMapM f).step = (do
    match it.step with
    | .yield it' out h => do
      match ← MonadAttach.attach (f out) with
      | ⟨none, hf⟩ =>
        pure <| .deflate <| .skip (it'.filterMapM f) (.yieldNone (out := out) h hf)
      | ⟨some out', hf⟩ =>
        pure <| .deflate <| .yield (it'.filterMapM f) out' (.yieldSome (out := out) h hf)
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
    [Monad n] [MonadAttach n] [LawfulMonad n] [MonadLiftT m n] :
  (it.filterM f).step = (do
    match it.step with
    | .yield it' out h => do
      match ← MonadAttach.attach (f out) with
      | ⟨.up false, hf⟩ =>
        pure <| .deflate <| .skip (it'.filterM f) (.yieldNone (out := out) h ⟨⟨.up false, hf⟩, rfl⟩)
      | ⟨.up true, hf⟩ =>
        pure <| .deflate <| .yield (it'.filterM f) out (.yieldSome (out := out) h ⟨⟨.up true, hf⟩, rfl⟩)
    | .skip it' h =>
      pure <| .deflate <| .skip (it'.filterM f) (.skip h)
    | .done h =>
      pure <| .deflate <| .done (.done h)) := by
  simp only [filterM_eq_toIter_filterM_toIterM, IterM.step_filterM, step]
  simp only [liftM, monadLift, pure_bind]
  generalize it.toIterM.step = step
  match step.inflate with
  | .yield it' out h =>
    simp only
    apply bind_congr; intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem Iter.step_mapM {f : β → n γ}
    [Monad n] [MonadAttach n] [LawfulMonad n] :
  (it.mapM f).step = (do
    match it.step with
    | .yield it' out h => do
      let out' ← MonadAttach.attach (f out)
      pure <| .deflate <| .yield (it'.mapM f) out'.val (.yieldSome h ⟨⟨out', out'.property⟩, rfl⟩)
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
  cases step.inflate using PlausibleIterStep.casesOn
  · simp only
    split <;> simp [*]
  · simp
  · simp

@[simp]
theorem Iter.toList_filterMap [Finite α Id]
    {f : β → Option γ} :
    (it.filterMap f).toList = it.toList.filterMap f := by
  simp [filterMap_eq_toIter_filterMap_toIterM, toList_eq_toList_toIterM, IterM.toList_filterMap]

@[simp]
theorem Iter.toList_mapWithPostcondition [Monad m] [LawfulMonad m] [Finite α Id]
    {f : β → PostconditionT m γ} :
    (it.mapWithPostcondition f).toList = it.toList.mapM (fun x => (f x).run) := by
  simp [Iter.mapWithPostcondition, IterM.toList_mapWithPostcondition, Iter.toList_eq_toList_toIterM]

@[simp]
theorem Iter.toList_mapM [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Finite α Id] {f : β → m γ} :
    (it.mapM f).toList = it.toList.mapM f := by
  simp [Iter.mapM_eq_toIter_mapM_toIterM, IterM.toList_mapM, Iter.toList_eq_toList_toIterM]

@[simp]
theorem Iter.toList_map [Finite α Id] {f : β → γ} :
    (it.map f).toList = it.toList.map f := by
  simp [map_eq_toIter_map_toIterM, IterM.toList_map, Iter.toList_eq_toList_toIterM]

@[simp]
theorem Iter.toList_filter [Finite α Id] {f : β → Bool} :
    (it.filter f).toList = it.toList.filter f := by
  simp [filter_eq_toIter_filter_toIterM, IterM.toList_filter, Iter.toList_eq_toList_toIterM]

@[simp]
theorem Iter.toList_filterMapWithPostcondition_filterMapWithPostcondition
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Finite α Id]
    {f : β → PostconditionT m (Option γ)} {g : γ → PostconditionT n (Option δ)} :
    ((it.filterMapWithPostcondition f).filterMapWithPostcondition g).toList =
      (it.filterMapWithPostcondition (m := n) (fun b => do
        match ← (haveI : MonadLift m n := ⟨monadLift⟩; f b) with
        | none => return none
        | some fb => g fb)).toList := by
  simp only [Iter.filterMapWithPostcondition]
  rw [IterM.toList_filterMapWithPostcondition_filterMapWithPostcondition,
    instMonadLiftTOfMonadLift_instMonadLiftTOfPure]
  rfl

@[simp]
theorem Iter.toList_mapWithPostcondition_mapWithPostcondition
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Finite α Id]
    {f : β → PostconditionT m γ} {g : γ → PostconditionT n δ} :
    ((it.mapWithPostcondition f).mapWithPostcondition g).toList =
      (it.mapWithPostcondition (m := n) (haveI : MonadLift m n := ⟨monadLift⟩; fun b => f b >>= g)).toList := by
  simp only [Iter.mapWithPostcondition]
  rw [IterM.toList_mapWithPostcondition_mapWithPostcondition,
    instMonadLiftTOfMonadLift_instMonadLiftTOfPure]

@[simp]
theorem Iter.toListRev_filterMap [Finite α Id]
    {f : β → Option γ} :
    (it.filterMap f).toListRev = it.toListRev.filterMap f := by
  simp [filterMap_eq_toIter_filterMap_toIterM, toListRev_eq_toListRev_toIterM, IterM.toListRev_filterMap]

@[simp]
theorem Iter.toListRev_map [Finite α Id]
    {f : β → γ} :
    (it.map f).toListRev = it.toListRev.map f := by
  simp [map_eq_toIter_map_toIterM, IterM.toListRev_map, Iter.toListRev_eq_toListRev_toIterM]

@[simp]
theorem Iter.toListRev_filter [Finite α Id]
    {f : β → Bool} :
    (it.filter f).toListRev = it.toListRev.filter f := by
  simp [filter_eq_toIter_filter_toIterM, IterM.toListRev_filter, Iter.toListRev_eq_toListRev_toIterM]

@[simp]
theorem Iter.toArray_filterMap [Finite α Id]
    {f : β → Option γ} :
    (it.filterMap f).toArray = it.toArray.filterMap f := by
  simp [filterMap_eq_toIter_filterMap_toIterM, toArray_eq_toArray_toIterM, IterM.toArray_filterMap]

@[simp]
theorem Iter.toArray_mapWithPostcondition [Monad m] [LawfulMonad m] [Finite α Id]
    {f : β → PostconditionT m γ} :
    (it.mapWithPostcondition f).toArray = it.toArray.mapM (fun x => (f x).run) := by
  simp [Iter.mapWithPostcondition, IterM.toArray_mapWithPostcondition, Iter.toArray_eq_toArray_toIterM]

@[simp]
theorem Iter.toArray_mapM [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [Finite α Id] {f : β → m γ} :
    (it.mapM f).toArray = it.toArray.mapM f := by
  simp [Iter.mapM_eq_toIter_mapM_toIterM, IterM.toArray_mapM, Iter.toArray_eq_toArray_toIterM]

@[simp]
theorem Iter.toArray_map [Finite α Id] {f : β → γ} :
    (it.map f).toArray = it.toArray.map f := by
  simp [map_eq_toIter_map_toIterM, IterM.toArray_map, Iter.toArray_eq_toArray_toIterM]

@[simp]
theorem Iter.toArray_filter[Finite α Id] {f : β → Bool} :
    (it.filter f).toArray = it.toArray.filter f := by
  simp [filter_eq_toIter_filter_toIterM, IterM.toArray_filter, Iter.toArray_eq_toArray_toIterM]

@[simp]
theorem Iter.toArray_filterMapWithPostcondition_filterMapWithPostcondition
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Finite α Id]
    {f : β → PostconditionT m (Option γ)} {g : γ → PostconditionT n (Option δ)} :
    ((it.filterMapWithPostcondition f).filterMapWithPostcondition g).toArray =
      (it.filterMapWithPostcondition (m := n) (fun b => do
        match ← (haveI : MonadLift m n := ⟨monadLift⟩; f b) with
        | none => return none
        | some fb => g fb)).toArray := by
  simp only [Iter.filterMapWithPostcondition]
  rw [IterM.toArray_filterMapWithPostcondition_filterMapWithPostcondition,
    instMonadLiftTOfMonadLift_instMonadLiftTOfPure]
  rfl

@[simp]
theorem Iter.toArray_mapWithPostcondition_mapWithPostcondition
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] [MonadLiftT m n] [LawfulMonadLiftT m n]
    [Finite α Id]
    {f : β → PostconditionT m γ} {g : γ → PostconditionT n δ} :
    ((it.mapWithPostcondition f).mapWithPostcondition g).toArray =
      (it.mapWithPostcondition (m := n) (haveI : MonadLift m n := ⟨monadLift⟩; fun b => f b >>= g)).toArray := by
  simp only [Iter.mapWithPostcondition]
  rw [IterM.toArray_mapWithPostcondition_mapWithPostcondition,
    instMonadLiftTOfMonadLift_instMonadLiftTOfPure]

section ForIn

theorem Iter.forIn_filterMapWithPostcondition
    [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT n o] [LawfulMonadLiftT n o] [Finite α Id]
    [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → PostconditionT n (Option β₂)} {init : γ}
    {g : β₂ → γ → o (ForInStep γ)} :
    forIn (it.filterMapWithPostcondition f) init g = forIn it init (fun out acc => do
        match ← (f out).run with
        | some c => g c acc
        | none => return .yield acc) := by
  simp [Iter.forIn_eq_forIn_toIterM, filterMapWithPostcondition, IterM.forIn_filterMapWithPostcondition,
    instMonadLiftTOfMonadLift_instMonadLiftTOfPure]; rfl

theorem Iter.forIn_filterMapM
    [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Finite α Id] [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → n (Option β₂)} {init : γ} {g : β₂ → γ → o (ForInStep γ)} :
    forIn (it.filterMapM f) init g = forIn it init (fun out acc => do
        match ← f out with
        | some c => g c acc
        | none => return .yield acc) := by
  simp [filterMapM, forIn_eq_forIn_toIterM, IterM.forIn_filterMapM,
    instMonadLiftTOfMonadLift_instMonadLiftTOfPure]; rfl

theorem Iter.forIn_filterMap
    [Monad n] [LawfulMonad n] [Finite α Id]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {it : Iter (α := α) β} {f : β → Option β₂} {init : γ} {g : β₂ → γ → n (ForInStep γ)} :
    forIn (it.filterMap f) init g = forIn it init (fun out acc => do
        match f out with
        | some c => g c acc
        | none => return .yield acc) := by
  simp [filterMap, forIn_eq_forIn_toIterM, IterM.forIn_filterMap]; rfl

theorem Iter.forIn_mapWithPostcondition
    [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT n o] [LawfulMonadLiftT n o] [Finite α Id]
    [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → PostconditionT n β₂} {init : γ}
    {g : β₂ → γ → o (ForInStep γ)} :
    forIn (it.mapWithPostcondition f) init g =
      forIn it init (fun out acc => do g (← (f out).run) acc) := by
  simp [mapWithPostcondition, forIn_eq_forIn_toIterM, IterM.forIn_mapWithPostcondition,
    instMonadLiftTOfMonadLift_instMonadLiftTOfPure]

theorem Iter.forIn_mapM
    [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Finite α Id]
    [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → n β₂} {init : γ} {g : β₂ → γ → o (ForInStep γ)} :
    forIn (it.mapM f) init g = forIn it init (fun out acc => do g (← f out) acc) := by
  rw [mapM, forIn_eq_forIn_toIterM, IterM.forIn_mapM, instMonadLiftTOfMonadLift_instMonadLiftTOfPure]

theorem Iter.forIn_map
    [Monad n] [LawfulMonad n]
    [Finite α Id] [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {it : Iter (α := α) β} {f : β → β₂} {init : γ} {g : β₂ → γ → n (ForInStep γ)} :
    forIn (it.map f) init g = forIn it init (fun out acc => do g (f out) acc) := by
  simp [map, forIn_eq_forIn_toIterM, IterM.forIn_map]

theorem Iter.forIn_filterWithPostcondition
    [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    [Finite α Id] [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → PostconditionT n (ULift Bool)} {init : γ}
    {g : β → γ → o (ForInStep γ)} :
    haveI : MonadLift n o := ⟨monadLift⟩
    forIn (it.filterWithPostcondition f) init g =
      forIn it init (fun out acc => do if (← (f out).run).down then g out acc else return .yield acc) := by
  simp [filterWithPostcondition, forIn_eq_forIn_toIterM, IterM.forIn_filterWithPostcondition,
    instMonadLiftTOfMonadLift_instMonadLiftTOfPure]

theorem Iter.forIn_filterM
    [Monad n] [LawfulMonad n] [Monad o] [LawfulMonad o]
    [MonadAttach n] [WeaklyLawfulMonadAttach n]
    [MonadLiftT n o] [LawfulMonadLiftT n o] [Finite α Id]
    [IteratorLoop α Id o] [LawfulIteratorLoop α Id o]
    {it : Iter (α := α) β} {f : β → n (ULift Bool)} {init : γ} {g : β → γ → o (ForInStep γ)} :
    forIn (it.filterM f) init g = forIn it init (fun out acc => do if (← f out).down then g out acc else return .yield acc) := by
  simp [filterM, forIn_eq_forIn_toIterM, IterM.forIn_filterM,
    instMonadLiftTOfMonadLift_instMonadLiftTOfPure]

theorem Iter.forIn_filter
    [Monad n] [LawfulMonad n]
    [Finite α Id] [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {it : Iter (α := α) β} {f : β → Bool} {init : γ} {g : β → γ → n (ForInStep γ)} :
    forIn (it.filter f) init g = forIn it init (fun out acc => do if f out then g out acc else return .yield acc) := by
  simp [filter, forIn_eq_forIn_toIterM, IterM.forIn_filter]

end ForIn

section Fold

theorem Iter.foldM_filterMapWithPostcondition {α β γ δ : Type w}
    {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [Monad o] [LawfulMonad n] [LawfulMonad o]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n (Option γ)} {g : δ → γ → o δ} {init : δ} {it : Iter (α := α) β} :
    (it.filterMapWithPostcondition f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do
          let some c ← (f b).run | pure d
          g d c) := by
  rw [filterMapWithPostcondition, IterM.foldM_filterMapWithPostcondition, foldM_eq_foldM_toIterM,
    instMonadLiftTOfMonadLift_instMonadLiftTOfPure]; rfl

theorem Iter.foldM_filterMapM {α β γ δ : Type w}
    {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [LawfulMonad o]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → n (Option γ)} {g : δ → γ → o δ} {init : δ} {it : Iter (α := α) β} :
    (it.filterMapM f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do
          let some c ← f b | pure d
          g d c) := by
  simp [filterMapM, IterM.foldM_filterMapM, foldM_eq_foldM_toIterM,
    instMonadLiftTOfMonadLift_instMonadLiftTOfPure]; rfl

theorem Iter.foldM_mapWithPostcondition {α β γ δ : Type w}
    {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α Id β] [Finite α Id]
    [Monad m] [Monad n] [Monad o] [LawfulMonad m][LawfulMonad n] [LawfulMonad o]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n γ} {g : δ → γ → o δ} {init : δ} {it : Iter (α := α) β} :
    (it.mapWithPostcondition f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do let c ← (f b).run; g d c) := by
  simp [mapWithPostcondition, IterM.foldM_mapWithPostcondition, foldM_eq_foldM_toIterM,
    instMonadLiftTOfMonadLift_instMonadLiftTOfPure]

theorem Iter.foldM_mapM {α β γ δ : Type w}
    {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [LawfulMonad o]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → n γ} {g : δ → γ → o δ} {init : δ} {it : Iter (α := α) β} :
    haveI : MonadLift n o := ⟨MonadLiftT.monadLift⟩
    (it.mapM f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do let c ← f b; g d c) := by
  simp [mapM, IterM.foldM_mapM, foldM_eq_foldM_toIterM,
    instMonadLiftTOfMonadLift_instMonadLiftTOfPure]

theorem Iter.foldM_filterWithPostcondition {α β δ : Type w}
    {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [Monad o] [LawfulMonad n] [LawfulMonad o]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → PostconditionT n (ULift Bool)} {g : δ → β → o δ} {init : δ} {it : Iter (α := α) β} :
    (it.filterWithPostcondition f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do if (← (f b).run).down then g d b else pure d) := by
  simp [filterWithPostcondition, IterM.foldM_filterWithPostcondition, foldM_eq_foldM_toIterM,
    instMonadLiftTOfMonadLift_instMonadLiftTOfPure]

theorem Iter.foldM_filterM {α β δ : Type w}
    {n : Type w → Type w''} {o : Type w → Type w'''}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [Monad o] [LawfulMonad o]
    [IteratorLoop α Id n] [IteratorLoop α Id o]
    [LawfulIteratorLoop α Id n] [LawfulIteratorLoop α Id o]
    [MonadLiftT n o] [LawfulMonadLiftT n o]
    {f : β → n (ULift Bool)} {g : δ → β → o δ} {init : δ} {it : Iter (α := α) β} :
    (it.filterM f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do if (← f b).down then g d b else pure d) := by
  simp [filterM, IterM.foldM_filterM, foldM_eq_foldM_toIterM,
    instMonadLiftTOfMonadLift_instMonadLiftTOfPure]

theorem Iter.foldM_filterMap {α β γ δ : Type w} {n : Type w → Type w''}
    [Iterator α Id β] [Finite α Id] [Monad n] [LawfulMonad n]
    [IteratorLoop α Id n]
    [LawfulIteratorLoop α Id n]
    {f : β → Option γ} {g : δ → γ → n δ} {init : δ} {it : Iter (α := α) β} :
    (it.filterMap f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do
          let some c := f b | pure d
          g d c) := by
  simp [filterMap, IterM.foldM_filterMap, foldM_eq_foldM_toIterM]; rfl

theorem Iter.foldM_map {α β γ δ : Type w} {n : Type w → Type w''}
    [Iterator α Id β] [Finite α Id] [Monad n] [LawfulMonad n]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → γ} {g : δ → γ → n δ} {init : δ} {it : Iter (α := α) β} :
    (it.map f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => do g d (f b)) := by
  simp [foldM_eq_forIn, forIn_map]

theorem Iter.foldM_filter {α β δ : Type w} {n : Type w → Type w''}
    [Iterator α Id β] [Finite α Id] [Monad n] [LawfulMonad n]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → Bool} {g : δ → β → n δ} {init : δ} {it : Iter (α := α) β} :
    (it.filter f).foldM (init := init) g =
      it.foldM (init := init) (fun d b => if f b then g d b else pure d) := by
  simp only [foldM_eq_forIn, forIn_filter]
  congr 1; ext out acc
  cases f out <;> simp

theorem Iter.fold_filterMapWithPostcondition {α β γ δ : Type w} {n : Type w → Type w''}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [LawfulMonad n]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → PostconditionT n (Option γ)} {g : δ → γ → δ} {init : δ} {it : Iter (α := α) β} :
    (it.filterMapWithPostcondition f).fold (init := init) g =
      it.foldM (init := init) (fun d b => do
          let some c ← (f b).run | pure d
          return g d c) := by
  simp [filterMapWithPostcondition, IterM.fold_filterMapWithPostcondition, foldM_eq_foldM_toIterM]
  rfl

theorem Iter.fold_filterMapM {α β γ δ : Type w} {n : Type w → Type w''}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → n (Option γ)} {g : δ → γ → δ} {init : δ} {it : Iter (α := α) β} :
    (it.filterMapM f).fold (init := init) g =
      it.foldM (init := init) (fun d b => do
          let some c ← f b | pure d
          return g d c) := by
  simp [filterMapM, IterM.fold_filterMapM, foldM_eq_foldM_toIterM]; rfl

theorem Iter.fold_mapWithPostcondition {α β γ δ : Type w} {n : Type w → Type w''}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [LawfulMonad n]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → PostconditionT n γ} {g : δ → γ → δ} {init : δ} {it : Iter (α := α) β} :
    (it.mapWithPostcondition f).fold (init := init) g =
      it.foldM (init := init) (fun d b => do let c ← (f b).run; return g d c) := by
  simp [mapWithPostcondition, IterM.fold_mapWithPostcondition, foldM_eq_foldM_toIterM]

theorem Iter.fold_mapM {α β γ δ : Type w} {n : Type w → Type w''}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → n γ} {g : δ → γ → δ} {init : δ} {it : Iter (α := α) β} :
    (it.mapM f).fold (init := init) g =
      it.foldM (init := init) (fun d b => do let c ← f b; return g d c) := by
  simp [mapM, IterM.fold_mapM, foldM_eq_foldM_toIterM]

theorem Iter.fold_filterWithPostcondition {α β δ : Type w}
    {n : Type w → Type w''}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [LawfulMonad n]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → PostconditionT n (ULift Bool)} {g : δ → β → δ} {init : δ} {it : Iter (α := α) β} :
    (it.filterWithPostcondition f).fold (init := init) g =
      it.foldM (init := init) (fun d b => return if (← (f b).run).down then g d b else d) := by
  simp [filterWithPostcondition, IterM.fold_filterWithPostcondition, foldM_eq_foldM_toIterM]

theorem Iter.fold_filterM {α β δ : Type w} {n : Type w → Type w''}
    [Iterator α Id β] [Finite α Id]
    [Monad n] [MonadAttach n] [LawfulMonad n] [WeaklyLawfulMonadAttach n]
    [IteratorLoop α Id n] [LawfulIteratorLoop α Id n]
    {f : β → n (ULift Bool)} {g : δ → β → δ} {init : δ} {it : Iter (α := α) β} :
    (it.filterM f).fold (init := init) g =
      it.foldM (init := init) (fun d b => return if (← f b).down then g d b else d) := by
  simp [filterM, IterM.fold_filterM, foldM_eq_foldM_toIterM]

theorem Iter.fold_filterMap {α β γ δ : Type w}
    [Iterator α Id β] [Finite α Id]
    [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    {f : β → Option γ} {g : δ → γ → δ} {init : δ} {it : Iter (α := α) β} :
    (it.filterMap f).fold (init := init) g =
      it.fold (init := init) (fun d b =>
          match f b with
          | some c => g d c
          | _ => d) := by
  simp [filterMap, IterM.fold_filterMap, fold_eq_fold_toIterM]; rfl

theorem Iter.fold_map {α β γ δ : Type w}
    [Iterator α Id β] [Finite α Id]
    [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    {f : β → γ} {g : δ → γ → δ} {init : δ} {it : Iter (α := α) β} :
    (it.map f).fold (init := init) g =
      it.fold (init := init) (fun d b => g d (f b)) := by
  simp [fold_eq_foldM, foldM_map]

theorem Iter.fold_filter {α β δ : Type w}
    [Iterator α Id β] [Finite α Id]
    [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    {f : β → Bool} {g : δ → β → δ} {init : δ} {it : Iter (α := α) β} :
    (it.filter f).fold (init := init) g =
      it.fold (init := init) (fun d b => if f b then g d b else d) := by
  simp [filter, IterM.fold_filter, fold_eq_fold_toIterM]

end Fold

section Count

@[simp]
theorem Iter.count_map {α β β' : Type w} [Iterator α Id β]
    [IteratorLoop α Id Id] [Finite α Id] [LawfulIteratorLoop α Id Id]
    {it : Iter (α := α) β} {f : β → β'} :
    (it.map f).count = it.count := by
  simp [map_eq_toIter_map_toIterM, count_eq_count_toIterM]

end Count

theorem Iter.anyM_filterMapM {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
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
    [Finite α Id] [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {it : Iter (α := α) β} {p : β → m Bool} :
    it.anyM p = ULift.down <$> (it.mapM (α := α) (pure (f := m))).anyM (fun x => ULift.up <$> p x) := by
  rw [anyM_eq_forIn, IterM.anyM_eq_forIn, map_eq_pure_bind]
  induction it using Iter.inductSteps with | step it ihy ihs =>
  rw [forIn_eq_match_step, IterM.forIn_eq_match_step, bind_assoc, step_mapM]
  cases it.step using PlausibleIterStep.casesOn
  · rename_i out _
    simp only [bind_assoc, pure_bind, map_eq_pure_bind, Shrink.inflate_deflate,
      liftM, monadLift]
    have {x : m Bool} : x = MonadAttach.attach (pure out) >>= (fun _ => x) := by
      rw (occs := [1]) [show x = pure out >>= (fun _ => x) by simp]
      conv => lhs; rw [← WeaklyLawfulMonadAttach.map_attach (x := pure out)]
      simp
    refine Eq.trans this ?_
    simp only [WeaklyLawfulMonadAttach.bind_attach_of_nonempty (x := pure out), pure_bind]
    split; rotate_left; rfl
    apply bind_congr; intro px
    split
    · simp
    · simp [ihy ‹_›]
  · simp [ihs ‹_›]
  · simp

theorem Iter.anyM_mapM {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    {it : Iter (α := α) β} {f : β → m β'} {p : β' → m (ULift Bool)} :
    (it.mapM f).anyM p = (it.mapM (pure (f := m))).anyM (fun x => do p (← f x)) := by
  rw [mapM_eq_toIter_mapM_toIterM, IterM.anyM_mapM, mapM_eq_toIter_mapM_toIterM]

theorem Iter.anyM_filterM {α β : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
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
    [Iterator α Id β] [Finite α Id] [IteratorLoop α Id m]
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m] [LawfulIteratorLoop α Id m]
    {it : Iter (α := α) β} {f : β → m (Option β')} {p : β' → Bool} :
    (it.filterMapM f).any p = (it.mapM (pure (f := m))).anyM (fun x => do
      match ← f x with
      | some fx => return .up (p fx)
      | none => return .up false) := by
  simp [IterM.any_eq_anyM, anyM_filterMapM]

theorem Iter.any_mapM {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [IteratorLoop α Id m]
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m] [LawfulIteratorLoop α Id m]
    {it : Iter (α := α) β} {f : β → m β'} {p : β' → Bool} :
    (it.mapM f).any p = (it.mapM pure).anyM (fun x => (.up <| p ·) <$> (f x)) := by
  simp [IterM.any_eq_anyM, anyM_mapM]

theorem Iter.any_filterM {α β : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [IteratorLoop α Id m]
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m] [LawfulIteratorLoop α Id m]
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
    [Iterator α Id β] [Finite α Id] [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
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
    [Finite α Id] [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [IteratorLoop α Id m] [LawfulIteratorLoop α Id m] {it : Iter (α := α) β} {p : β → m Bool} :
    it.allM p = ULift.down <$> (it.mapM (α := α) (pure (f := m))).allM (fun x => ULift.up <$> p x) := by
  simp [allM_eq_not_anyM_not, anyM_eq_anyM_mapM_pure, IterM.allM_eq_not_anyM_not]

theorem Iter.allM_mapM {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    {it : Iter (α := α) β} {f : β → m β'} {p : β' → m (ULift Bool)} :
    (it.mapM f).allM p = (it.mapM (pure (f := m))).allM (fun x => do p (← f x)) := by
  rw [mapM_eq_toIter_mapM_toIterM, IterM.allM_mapM, mapM_eq_toIter_mapM_toIterM]

theorem Iter.allM_filterM {α β : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
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
    [Iterator α Id β] [Finite α Id] [IteratorLoop α Id m]
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [LawfulIteratorLoop α Id m]
    {it : Iter (α := α) β} {f : β → m (Option β')} {p : β' → Bool} :
    (it.filterMapM f).all p = (it.mapM (pure (f := m))).allM (fun x => do
      match ← f x with
      | some fx => return .up (p fx)
      | none => return .up true) := by
  simp [IterM.all_eq_allM, allM_filterMapM]

theorem Iter.all_mapM {α β β' : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [IteratorLoop α Id m]
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m]
    [LawfulIteratorLoop α Id m] {it : Iter (α := α) β} {f : β → m β'} {p : β' → Bool} :
    (it.mapM f).all p = (it.mapM pure).allM (fun x => (.up <| p ·) <$> (f x)) := by
  simp [IterM.all_eq_allM, allM_mapM]

theorem Iter.all_filterM {α β : Type w} {m : Type w → Type w'}
    [Iterator α Id β] [Finite α Id] [IteratorLoop α Id m]
    [Monad m] [MonadAttach m] [LawfulMonad m] [WeaklyLawfulMonadAttach m] [LawfulIteratorLoop α Id m]
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

end Std
