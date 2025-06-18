/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
import Init.Data.Iterators.Lemmas.Consumers.Collect
import all Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop
import all Init.Data.Iterators.Consumers.Loop

namespace Std.Iterators

theorem Iter.forIn_eq {α β : Type w} [Iterator α Id β] [Finite α Id]
    {m : Type w → Type w''} [Monad m] [IteratorLoop α Id m] [hl : LawfulIteratorLoop α Id m]
    {γ : Type w} {it : Iter (α := α) β} {init : γ}
    {f : (b : β) → γ → m (ForInStep γ)} :
    ForIn.forIn it init f =
      IterM.DefaultConsumers.forIn (fun _ c => pure c.run) γ (fun _ _ _ => True)
        IteratorLoop.wellFounded_of_finite it.toIterM init
          (fun out acc => (⟨·, .intro⟩) <$>
            f out acc) := by
  cases hl.lawful; rfl

theorem Iter.forIn_eq_forIn_toIterM {α β : Type w} [Iterator α Id β]
    [Finite α Id] {m : Type w → Type w''} [Monad m] [LawfulMonad m]
    [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {γ : Type w} {it : Iter (α := α) β} {init : γ}
    {f : β → γ → m (ForInStep γ)} :
    ForIn.forIn it init f =
      letI : MonadLift Id m := ⟨Std.Internal.idToMonad (α := _)⟩
      ForIn.forIn it.toIterM init f := by
  rfl

theorem Iter.forIn_eq_match_step {α β : Type w} [Iterator α Id β]
    [Finite α Id] {m : Type w → Type w''} [Monad m] [LawfulMonad m]
    [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {γ : Type w} {it : Iter (α := α) β} {init : γ}
    {f : β → γ → m (ForInStep γ)} :
    ForIn.forIn it init f = (do
      match it.step with
      | .yield it' out _ =>
        match ← f out init with
        | .yield c => ForIn.forIn it' c f
        | .done c => return c
      | .skip it' _ => ForIn.forIn it' init f
      | .done _ => return init) := by
  rw [Iter.forIn_eq_forIn_toIterM, @IterM.forIn_eq_match_step, Iter.step]
  simp only [liftM, monadLift, pure_bind]
  generalize it.toIterM.step = step
  cases step using PlausibleIterStep.casesOn
  · apply bind_congr
    intro forInStep
    rfl
  · rfl
  · rfl

theorem Iter.forIn_toList {α β : Type w} [Iterator α Id β]
    [Finite α Id] {m : Type w → Type w''} [Monad m] [LawfulMonad m]
    [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    {γ : Type w} {it : Iter (α := α) β} {init : γ}
    {f : β → γ → m (ForInStep γ)} :
    ForIn.forIn it.toList init f = ForIn.forIn it init f := by
  rw [List.forIn_eq_foldlM]
  induction it using Iter.inductSteps generalizing init with case step it ihy ihs =>
  rw [forIn_eq_match_step, Iter.toList_eq_match_step]
  simp only [map_eq_pure_bind]
  generalize it.step = step
  cases step using PlausibleIterStep.casesOn
  · rename_i it' out h
    simp only [List.foldlM_cons, bind_pure_comp, map_bind]
    apply bind_congr
    intro forInStep
    cases forInStep
    · induction it'.toList <;> simp [*]
    · simp only [ForIn.forIn, forIn', List.forIn'] at ihy
      simp [ihy h, forIn_eq_forIn_toIterM]
  · rename_i it' h
    simp only [bind_pure_comp]
    rw [ihs h]
  · simp

theorem Iter.foldM_eq_forIn {α β γ : Type w} [Iterator α Id β] [Finite α Id] {m : Type w → Type w'}
    [Monad m] [IteratorLoop α Id m] {f : γ → β → m γ}
    {init : γ} {it : Iter (α := α) β} :
    it.foldM (init := init) f = ForIn.forIn it init (fun x acc => ForInStep.yield <$> f acc x) :=
  (rfl)

theorem Iter.foldM_eq_foldM_toIterM {α β : Type w} [Iterator α Id β]
    [Finite α Id] {m : Type w → Type w''} [Monad m] [LawfulMonad m]
    [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {γ : Type w} {it : Iter (α := α) β} {init : γ} {f : γ → β → m γ} :
    it.foldM (init := init) f = letI : MonadLift Id m := ⟨pure⟩; it.toIterM.foldM (init := init) f :=
  (rfl)

theorem Iter.forIn_yield_eq_foldM {α β γ δ : Type w} [Iterator α Id β]
    [Finite α Id] {m : Type w → Type w''} [Monad m] [LawfulMonad m] [IteratorLoop α Id m]
    [LawfulIteratorLoop α Id m] {f : β → γ → m δ} {g : β → γ → δ → γ} {init : γ}
    {it : Iter (α := α) β} :
    ForIn.forIn it init (fun c b => (fun d => .yield (g c b d)) <$> f c b) =
      it.foldM (fun b c => g c b <$> f c b) init := by
  simp [Iter.foldM_eq_forIn]

theorem Iter.foldM_eq_match_step {α β γ : Type w} [Iterator α Id β] [Finite α Id]
    {m : Type w → Type w'} [Monad m] [LawfulMonad m] [IteratorLoop α Id m]
    [LawfulIteratorLoop α Id m] {f : γ → β → m γ} {init : γ} {it : Iter (α := α) β} :
    it.foldM (init := init) f = (do
      match it.step with
      | .yield it' out _ => it'.foldM (init := ← f init out) f
      | .skip it' _ => it'.foldM (init := init) f
      | .done _ => return init) := by
  rw [Iter.foldM_eq_forIn, Iter.forIn_eq_match_step]
  generalize it.step = step
  cases step using PlausibleIterStep.casesOn <;> simp [foldM_eq_forIn]

theorem Iter.foldlM_toList {α β γ : Type w} [Iterator α Id β] [Finite α Id] {m : Type w → Type w'}
    [Monad m] [LawfulMonad m] [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    {f : γ → β → m γ}
    {init : γ} {it : Iter (α := α) β} :
    it.toList.foldlM (init := init) f = it.foldM (init := init) f := by
  rw [Iter.foldM_eq_forIn, ← Iter.forIn_toList]
  simp only [List.forIn_yield_eq_foldlM, id_map']

theorem IterM.forIn_eq_foldM {α β : Type w} [Iterator α Id β]
    [Finite α Id] {m : Type w → Type w''} [Monad m] [LawfulMonad m]
    [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    {γ : Type w} {it : Iter (α := α) β} {init : γ}
    {f : β → γ → m (ForInStep γ)} :
    forIn it init f = ForInStep.value <$>
      it.foldM (fun c b => match c with
        | .yield c => f b c
        | .done c => pure (.done c)) (ForInStep.yield init) := by
  simp only [← Iter.forIn_toList, List.forIn_eq_foldlM, ← Iter.foldlM_toList]; rfl

theorem Iter.fold_eq_forIn {α β γ : Type w} [Iterator α Id β]
    [Finite α Id] [IteratorLoop α Id Id] {f : γ → β → γ} {init : γ} {it : Iter (α := α) β} :
    it.fold (init := init) f =
      (ForIn.forIn (m := Id) it init (fun x acc => pure (ForInStep.yield (f acc x)))).run := by
  rfl

theorem Iter.fold_eq_foldM {α β γ : Type w} [Iterator α Id β]
    [Finite α Id] [IteratorLoop α Id Id] {f : γ → β → γ} {init : γ}
    {it : Iter (α := α) β} :
    it.fold (init := init) f = (it.foldM (m := Id) (init := init) (pure <| f · ·)).run := by
  simp [foldM_eq_forIn, fold_eq_forIn]

@[simp]
theorem Iter.forIn_pure_yield_eq_fold {α β γ : Type w} [Iterator α Id β]
    [Finite α Id] [IteratorLoop α Id Id]
    [LawfulIteratorLoop α Id Id] {f : β → γ → γ} {init : γ}
    {it : Iter (α := α) β} :
    ForIn.forIn (m := Id) it init (fun c b => pure (.yield (f c b))) =
      pure (it.fold (fun b c => f c b) init) := by
  simp only [fold_eq_forIn]
  rfl

theorem Iter.fold_eq_match_step {α β γ : Type w} [Iterator α Id β] [Finite α Id]
    [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    {f : γ → β → γ} {init : γ} {it : Iter (α := α) β} :
    it.fold (init := init) f = (match it.step with
      | .yield it' out _ => it'.fold (init := f init out) f
      | .skip it' _ => it'.fold (init := init) f
      | .done _ => init) := by
  rw [fold_eq_foldM, foldM_eq_match_step]
  simp only [fold_eq_foldM]
  generalize it.step = step
  cases step using PlausibleIterStep.casesOn <;> simp

theorem Iter.foldl_toList {α β γ : Type w} [Iterator α Id β] [Finite α Id]
    [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    {f : γ → β → γ} {init : γ} {it : Iter (α := α) β} :
    it.toList.foldl (init := init) f = it.fold (init := init) f := by
  rw [fold_eq_foldM, List.foldl_eq_foldlM, ← Iter.foldlM_toList]

end Std.Iterators
