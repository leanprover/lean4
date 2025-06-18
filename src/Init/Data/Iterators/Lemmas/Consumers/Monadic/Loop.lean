/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect
import all Init.Data.Iterators.Consumers.Monadic.Loop

namespace Std.Iterators

theorem IterM.DefaultConsumers.forIn_eq_match_step {α β : Type w} {m : Type w → Type w'}
    [Iterator α m β]
    {n : Type w → Type w''} [Monad n]
    {lift : ∀ γ, m γ → n γ} {γ : Type w}
    {plausible_forInStep : β → γ → ForInStep γ → Prop}
    {wf : IteratorLoop.WellFounded α m plausible_forInStep}
    {it : IterM (α := α) m β} {init : γ}
    {f : (b : β) → (c : γ) → n (Subtype (plausible_forInStep b c))} :
    IterM.DefaultConsumers.forIn lift γ plausible_forInStep wf it init f = (do
      match ← lift _ it.step with
      | .yield it' out _ =>
        match ← f out init with
        | ⟨.yield c, _⟩ =>
          IterM.DefaultConsumers.forIn lift _ plausible_forInStep wf it' c
            fun out acc => f out acc
        | ⟨.done c, _⟩ => return c
      | .skip it' _ =>
        IterM.DefaultConsumers.forIn lift _ plausible_forInStep wf it' init
          fun out acc => f out acc
      | .done _ => return init) := by
  rw [forIn]
  apply bind_congr
  intro step
  cases step using PlausibleIterStep.casesOn <;> rfl

theorem IterM.forIn_eq {α β : Type w} {m : Type w → Type w'} [Iterator α m β] [Finite α m]
    {n : Type w → Type w''} [Monad n] [IteratorLoop α m n] [hl : LawfulIteratorLoop α m n]
    [MonadLiftT m n] {γ : Type w} {it : IterM (α := α) m β} {init : γ}
    {f : β → γ → n (ForInStep γ)} :
    ForIn.forIn it init f = IterM.DefaultConsumers.forIn (fun _ => monadLift) γ (fun _ _ _ => True)
        IteratorLoop.wellFounded_of_finite it init (fun out acc => (⟨·, .intro⟩) <$> f out acc) := by
  cases hl.lawful; rfl

theorem IterM.forIn_eq_match_step {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] {n : Type w → Type w''} [Monad n] [LawfulMonad n]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] {γ : Type w} {it : IterM (α := α) m β} {init : γ}
    {f : β → γ → n (ForInStep γ)} :
    ForIn.forIn it init f = (do
      match ← it.step with
      | .yield it' out _ =>
        match ← f out init with
        | .yield c => ForIn.forIn it' c f
        | .done c => return c
      | .skip it' _ => ForIn.forIn it' init f
      | .done _ => return init) := by
  rw [IterM.forIn_eq, DefaultConsumers.forIn_eq_match_step]
  apply bind_congr
  intro step
  cases step using PlausibleIterStep.casesOn
  · simp only [map_eq_pure_bind, bind_assoc]
    apply bind_congr
    intro forInStep
    cases forInStep <;> simp [IterM.forIn_eq]
  · simp [IterM.forIn_eq]
  · simp

theorem IterM.forM_eq_forIn {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] {n : Type w → Type w''} [Monad n] [LawfulMonad n]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] {it : IterM (α := α) m β}
    {f : β → n PUnit} :
    ForM.forM it f = ForIn.forIn it PUnit.unit (fun out _ => do f out; return .yield .unit) :=
  rfl

theorem IterM.forM_eq_match_step {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] {n : Type w → Type w''} [Monad n] [LawfulMonad n]
    [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] {it : IterM (α := α) m β}
    {f : β → n PUnit} :
    ForM.forM it f = (do
      match ← it.step with
      | .yield it' out _ =>
        f out
        ForM.forM it' f
      | .skip it' _ => ForM.forM it' f
      | .done _ => return) := by
  rw [forM_eq_forIn, forIn_eq_match_step]
  apply bind_congr
  intro step
  cases step using PlausibleIterStep.casesOn <;> simp [forM_eq_forIn]

theorem IterM.foldM_eq_forIn {α β γ : Type w} {m : Type w → Type w'} [Iterator α m β] [Finite α m]
    {n : Type w → Type w''} [Monad n] [IteratorLoop α m n] [MonadLiftT m n] {f : γ → β → n γ}
    {init : γ} {it : IterM (α := α) m β} :
    it.foldM (init := init) f = ForIn.forIn it init (fun x acc => ForInStep.yield <$> f acc x) :=
  (rfl)

theorem IterM.forIn_yield_eq_foldM {α β γ δ : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] {n : Type w → Type w''} [Monad n] [LawfulMonad n] [IteratorLoop α m n]
    [LawfulIteratorLoop α m n] [MonadLiftT m n] {f : β → γ → n δ} {g : β → γ → δ → γ} {init : γ}
    {it : IterM (α := α) m β} :
    ForIn.forIn it init (fun c b => (fun d => .yield (g c b d)) <$> f c b) =
      it.foldM (fun b c => g c b <$> f c b) init := by
  simp [IterM.foldM_eq_forIn]

theorem IterM.foldM_eq_match_step {α β γ : Type w} {m : Type w → Type w'} [Iterator α m β] [Finite α m]
    {n : Type w → Type w''} [Monad n] [LawfulMonad n] [IteratorLoop α m n] [LawfulIteratorLoop α m n]
    [MonadLiftT m n] {f : γ → β → n γ} {init : γ} {it : IterM (α := α) m β} :
    it.foldM (init := init) f = (do
      match ← it.step with
      | .yield it' out _ => it'.foldM (init := ← f init out) f
      | .skip it' _ => it'.foldM (init := init) f
      | .done _ => return init) := by
  rw [IterM.foldM_eq_forIn, IterM.forIn_eq_match_step]
  apply bind_congr
  intro step
  cases step using PlausibleIterStep.casesOn <;> simp [foldM_eq_forIn]

theorem IterM.fold_eq_forIn {α β γ : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m]
    [IteratorLoop α m m] {f : γ → β → γ} {init : γ} {it : IterM (α := α) m β} :
    it.fold (init := init) f =
      ForIn.forIn (m := m) it init (fun x acc => pure (ForInStep.yield (f acc x))) := by
  rfl

theorem IterM.fold_eq_foldM {α β γ : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] {f : γ → β → γ} {init : γ}
    {it : IterM (α := α) m β} :
    it.fold (init := init) f = it.foldM (init := init) (pure <| f · ·) := by
  simp [foldM_eq_forIn, fold_eq_forIn]

@[simp]
theorem IterM.forIn_pure_yield_eq_fold {α β γ : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m]
    [LawfulIteratorLoop α m m] {f : β → γ → γ} {init : γ}
    {it : IterM (α := α) m β} :
    ForIn.forIn it init (fun c b => pure (.yield (f c b))) =
      it.fold (fun b c => f c b) init := by
  simp [IterM.fold_eq_forIn]

theorem IterM.fold_eq_match_step {α β γ : Type w} {m : Type w → Type w'} [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {f : γ → β → γ} {init : γ} {it : IterM (α := α) m β} :
    it.fold (init := init) f = (do
      match ← it.step with
      | .yield it' out _ => it'.fold (init := f init out) f
      | .skip it' _ => it'.fold (init := init) f
      | .done _ => return init) := by
  rw [fold_eq_foldM, foldM_eq_match_step]
  simp only [fold_eq_foldM]
  apply bind_congr
  intro step
  cases step using PlausibleIterStep.casesOn <;> simp

theorem IterM.toList_eq_fold {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {it : IterM (α := α) m β} :
    it.toList = it.fold (init := []) (fun l out => l ++ [out]) := by
  suffices h : ∀ l' : List β, (l' ++ ·) <$> it.toList =
      it.fold (init := l') (fun l out => l ++ [out]) by
    specialize h []
    simpa using h
  induction it using IterM.inductSteps with | step it ihy ihs =>
  intro l'
  rw [IterM.toList_eq_match_step, IterM.fold_eq_match_step]
  simp only [map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro step
  cases step using PlausibleIterStep.casesOn
  · rename_i it' out h
    specialize ihy h (l' ++ [out])
    simpa using ihy
  · rename_i it' h
    simp [ihs h]
  · simp

theorem IterM.drain_eq_fold {α β : Type w} {m : Type w → Type w'} [Iterator α m β] [Finite α m]
    [Monad m] [IteratorLoop α m m] {it : IterM (α := α) m β} :
    it.drain = it.fold (init := PUnit.unit) (fun _ _ => .unit) :=
  (rfl)

theorem IterM.drain_eq_foldM {α β : Type w} {m : Type w → Type w'} [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m] [IteratorLoop α m m] {it : IterM (α := α) m β} :
    it.drain = it.foldM (init := PUnit.unit) (fun _ _ => pure .unit) := by
  simp [IterM.drain_eq_fold, IterM.fold_eq_foldM]

theorem IterM.drain_eq_forIn {α β : Type w} {m : Type w → Type w'}  [Iterator α m β] [Finite α m]
    [Monad m] [IteratorLoop α m m] {it : IterM (α := α) m β} :
    it.drain = ForIn.forIn (m := m) it PUnit.unit (fun _ _ => pure (ForInStep.yield .unit)) := by
  simp [IterM.drain_eq_fold, IterM.fold_eq_forIn]

theorem IterM.drain_eq_match_step {α β : Type w} {m : Type w → Type w'} [Iterator α m β] [Finite α m]
    [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    {it : IterM (α := α) m β} :
    it.drain = (do
      match ← it.step with
      | .yield it' _ _ => it'.drain
      | .skip it' _ => it'.drain
      | .done _ => return .unit) := by
  rw [IterM.drain_eq_fold, IterM.fold_eq_match_step]
  simp [IterM.drain_eq_fold]

theorem IterM.drain_eq_map_toList {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {it : IterM (α := α) m β} :
    it.drain = (fun _ => .unit) <$> it.toList := by
  induction it using IterM.inductSteps with | step it ihy ihs =>
  rw [IterM.drain_eq_match_step, IterM.toList_eq_match_step]
  simp only [map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro step
  cases step using PlausibleIterStep.casesOn
  · rename_i it' out h
    simp [ihy h]
  · rename_i it' h
    simp [ihs h]
  · simp

theorem IterM.drain_eq_map_toListRev {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {it : IterM (α := α) m β} :
    it.drain = (fun _ => .unit) <$> it.toListRev := by
  simp [IterM.drain_eq_map_toList, IterM.toListRev_eq]

theorem IterM.drain_eq_map_toArray {α β : Type w} {m : Type w → Type w'} [Iterator α m β]
    [Finite α m] [Monad m] [LawfulMonad m] [IteratorLoop α m m] [LawfulIteratorLoop α m m]
    [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {it : IterM (α := α) m β} :
    it.drain = (fun _ => .unit) <$> it.toList := by
  simp [IterM.drain_eq_map_toList]

end Std.Iterators
