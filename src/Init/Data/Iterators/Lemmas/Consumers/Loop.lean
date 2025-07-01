/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Lemmas.Consumers.Collect
public import all Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop
public import all Init.Data.Iterators.Consumers.Loop
public import all Init.Data.Iterators.Consumers.Monadic.Collect

public section

namespace Std.Iterators

theorem Iter.forIn'_eq {α β : Type w} [Iterator α Id β] [Finite α Id]
    {m : Type x → Type x'} [Monad m] [IteratorLoop α Id m] [hl : LawfulIteratorLoop α Id m]
    {γ : Type x} {it : Iter (α := α) β} {init : γ}
    {f : (b : β) → it.IsPlausibleIndirectOutput b → γ → m (ForInStep γ)} :
    letI : ForIn' m (Iter (α := α) β) β _ := Iter.instForIn'
    ForIn'.forIn' it init f =
      IterM.DefaultConsumers.forIn' (fun _ _ f x => f x.run) γ (fun _ _ _ => True)
        IteratorLoop.wellFounded_of_finite it.toIterM init _ (fun _ => id)
          (fun out h acc => (⟨·, .intro⟩) <$>
            f out (Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM.mpr h) acc) := by
  cases hl.lawful; rfl

theorem Iter.forIn_eq {α β : Type w} [Iterator α Id β] [Finite α Id]
    {m : Type x → Type x'} [Monad m] [IteratorLoop α Id m] [hl : LawfulIteratorLoop α Id m]
    {γ : Type x} {it : Iter (α := α) β} {init : γ}
    {f : (b : β) → γ → m (ForInStep γ)} :
    ForIn.forIn it init f =
      IterM.DefaultConsumers.forIn' (fun _ _ f c => f c.run) γ (fun _ _ _ => True)
        IteratorLoop.wellFounded_of_finite it.toIterM init _ (fun _ => id)
          (fun out _ acc => (⟨·, .intro⟩) <$>
            f out acc) := by
  cases hl.lawful; rfl

theorem Iter.forIn'_eq_forIn'_toIterM {α β : Type w} [Iterator α Id β]
    [Finite α Id] {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {γ : Type w} {it : Iter (α := α) β} {init : γ}
    {f : (out : β) → _ → γ → m (ForInStep γ)} :
    letI : ForIn' m (Iter (α := α) β) β _ := Iter.instForIn'
    ForIn'.forIn' it init f =
      letI : ForIn' m (IterM (α := α) Id β) β _ := IterM.instForIn'
      ForIn'.forIn' it.toIterM init
        (fun out h acc => f out (isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM.mpr h) acc) := by
  simp [ForIn'.forIn', Iter.instForIn', IterM.instForIn', monadLift]

theorem Iter.forIn_eq_forIn_toIterM {α β : Type w} [Iterator α Id β]
    [Finite α Id] {m : Type w → Type w''} [Monad m] [LawfulMonad m]
    [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {γ : Type w} {it : Iter (α := α) β} {init : γ}
    {f : β → γ → m (ForInStep γ)} :
    ForIn.forIn it init f =
      ForIn.forIn it.toIterM init f := by
  simp [forIn_eq_forIn', forIn'_eq_forIn'_toIterM, -forIn'_eq_forIn]

theorem Iter.forIn'_eq_match_step {α β : Type w} [Iterator α Id β]
    [Finite α Id] {m : Type x → Type x''} [Monad m] [LawfulMonad m]
    [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {γ : Type x} {it : Iter (α := α) β} {init : γ}
    {f : (out : β) → _ → γ → m (ForInStep γ)} :
    letI : ForIn' m (Iter (α := α) β) β _ := Iter.instForIn'
    ForIn'.forIn' it init f = (do
      match it.step with
      | .yield it' out h =>
        match ← f out (.direct ⟨_, h⟩) init with
        | .yield c =>
          ForIn'.forIn' it' c
            fun out h'' acc => f out (.indirect ⟨_, rfl, h⟩ h'') acc
        | .done c => return c
      | .skip it' h =>
          ForIn'.forIn' it' init
            fun out h' acc => f out (.indirect ⟨_, rfl, h⟩ h') acc
      | .done _ => return init) := by
  simp only [forIn'_eq]
  rw [IterM.DefaultConsumers.forIn'_eq_match_step]
  simp only [bind_map_left, Iter.step]
  cases it.toIterM.step.run using PlausibleIterStep.casesOn
  · simp only [IterM.Step.toPure_yield, PlausibleIterStep.yield, toIter_toIterM, toIterM_toIter]
    apply bind_congr
    intro forInStep
    cases forInStep
    · simp
    · simp only
      apply IterM.DefaultConsumers.forIn'_eq_forIn'
      intros; congr
  · simp only
    apply IterM.DefaultConsumers.forIn'_eq_forIn'
    intros; congr
  · simp

theorem Iter.forIn_eq_match_step {α β : Type w} [Iterator α Id β]
    [Finite α Id] {m : Type x → Type x'} [Monad m] [LawfulMonad m]
    [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {γ : Type x} {it : Iter (α := α) β} {init : γ}
    {f : β → γ → m (ForInStep γ)} :
    ForIn.forIn it init f = (do
      match it.step with
      | .yield it' out _ =>
        match ← f out init with
        | .yield c => ForIn.forIn it' c f
        | .done c => return c
      | .skip it' _ => ForIn.forIn it' init f
      | .done _ => return init) := by
  simp only [forIn_eq_forIn']
  exact forIn'_eq_match_step

private theorem Iter.forIn'_toList.aux {ρ : Type u} {α : Type v} {γ : Type x} {m : Type x → Type x'}
    [Monad m] {_ : Membership α ρ} [ForIn' m ρ α inferInstance]
    {r s : ρ} {init : γ} {f : (a : α) → _ → γ → m (ForInStep γ)} (h : r = s) :
    forIn' r init f = forIn' s init (fun a h' acc => f a (h ▸ h') acc) := by
  cases h; rfl

theorem Iter.isPlausibleStep_iff_step_eq {α β} [Iterator α Id β]
    [IteratorCollect α Id Id] [Finite α Id]
    [LawfulIteratorCollect α Id Id] [LawfulDeterministicIterator α Id]
    {it : Iter (α := α) β} {step} :
    it.IsPlausibleStep step ↔ it.step.val = step := by
  obtain ⟨step', hs'⟩ := LawfulDeterministicIterator.isPlausibleStep_eq_eq (it := it.toIterM)
  have hs := it.step.property
  simp only [Iter.IsPlausibleStep, hs'] at hs
  cases hs
  simp only [IsPlausibleStep, hs', Iter.step, IterM.Step.toPure, toIter_toIterM,
    IterStep.mapIterator_mapIterator, toIterM_comp_toIter, IterStep.mapIterator_id]
  simp only [Eq.comm (b := step)]
  constructor
  · intro h
    replace h := congrArg (IterStep.mapIterator IterM.toIter) h
    simpa using h
  · intro h
    replace h := congrArg (IterStep.mapIterator Iter.toIterM) h
    simpa using h

theorem Iter.mem_toList_iff_isPlausibleIndirectOutput {α β} [Iterator α Id β]
    [IteratorCollect α Id Id] [Finite α Id]
    [LawfulIteratorCollect α Id Id] [LawfulDeterministicIterator α Id]
    {it : Iter (α := α) β} {out : β} :
    out ∈ it.toList ↔ it.IsPlausibleIndirectOutput out := by
  induction it using Iter.inductSteps with | step it ihy ihs =>
  rw [toList_eq_match_step]
  constructor
  · intro h
    cases heq : it.step using PlausibleIterStep.casesOn <;> simp only [heq] at h
    · rename_i it' out hp
      cases List.mem_cons.mp h <;> rename_i hmem
      · cases hmem
        simp only [Iter.IsPlausibleStep, IterStep.mapIterator_yield] at hp
        exact Iter.IsPlausibleIndirectOutput.direct ⟨_, hp⟩
      · apply Iter.IsPlausibleIndirectOutput.indirect
        · exact ⟨_, rfl, ‹_›⟩
        · exact (ihy ‹_›).mp hmem
    · apply Iter.IsPlausibleIndirectOutput.indirect
      · exact ⟨_, rfl, ‹_›⟩
      · exact (ihs ‹_›).mp h
    · cases h
  · intro hp
    cases hp
    · rename_i hp
      simp only [Iter.isPlausibleOutput_iff_exists, Iter.isPlausibleStep_iff_step_eq] at hp
      obtain ⟨it', hp⟩ := hp
      split <;> simp_all
    · rename_i it' h₁ h₂
      cases heq : it.step using PlausibleIterStep.casesOn <;> simp only
      · apply List.mem_cons_of_mem
        simp only [Iter.isPlausibleSuccessorOf_iff_exists, Iter.isPlausibleStep_iff_step_eq] at h₁
        obtain ⟨step, h₁, rfl⟩ := h₁
        simp only [heq, IterStep.successor, Option.some.injEq] at h₁
        cases h₁
        simp only [ihy ‹_›]
        exact h₂
      · simp only [Iter.isPlausibleSuccessorOf_iff_exists, Iter.isPlausibleStep_iff_step_eq] at h₁
        obtain ⟨step, h₁, rfl⟩ := h₁
        simp only [heq, IterStep.successor, Option.some.injEq] at h₁
        cases h₁
        rw [ihs ‹_›]
        exact h₂
      · simp only [Iter.isPlausibleSuccessorOf_iff_exists, Iter.isPlausibleStep_iff_step_eq] at h₁
        obtain ⟨step, h₁, rfl⟩ := h₁
        simp [heq, IterStep.successor] at h₁

theorem Iter.forIn'_toList {α β : Type w} [Iterator α Id β]
    [Finite α Id] {m : Type x → Type x'} [Monad m] [LawfulMonad m]
    [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    [LawfulDeterministicIterator α Id]
    {γ : Type x} {it : Iter (α := α) β} {init : γ}
    {f : (out : β) → _ → γ → m (ForInStep γ)} :
    letI : ForIn' m (Iter (α := α) β) β _ := Iter.instForIn'
    ForIn'.forIn' it.toList init f = ForIn'.forIn' it init (fun out h acc => f out (Iter.mem_toList_iff_isPlausibleIndirectOutput.mpr h) acc) := by
  induction it using Iter.inductSteps generalizing init with case step it ihy ihs =>
  have := it.toList_eq_match_step
  generalize hs : it.step = step at this
  rw [forIn'_toList.aux this]
  rw [forIn'_eq_match_step]
  rw [List.forIn'_eq_foldlM] at *
  simp only [map_eq_pure_bind, hs]
  cases step using PlausibleIterStep.casesOn
  · rename_i it' out h
    simp only [List.attach_cons, List.foldlM_cons, bind_pure_comp, map_bind]
    apply bind_congr
    intro forInStep
    cases forInStep
    · induction it'.toList.attach <;> simp [*]
    · simp only [List.foldlM_map]
      simp only [List.forIn'_eq_foldlM] at ihy
      simp only at this
      simp only [ihy h (f := fun out h acc => f out (by rw [this]; exact List.mem_cons_of_mem _ h) acc)]
  · rename_i it' h
    simp only [bind_pure_comp]
    simp only [List.forIn'_eq_foldlM] at ihs
    simp only at this
    simp only [ihs h (f := fun out h acc => f out (this ▸ h) acc)]
  · simp

theorem Iter.forIn'_eq_forIn'_toList {α β : Type w} [Iterator α Id β]
    [Finite α Id] {m : Type x → Type x'} [Monad m] [LawfulMonad m]
    [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    [LawfulDeterministicIterator α Id]
    {γ : Type x} {it : Iter (α := α) β} {init : γ}
    {f : (out : β) → _ → γ → m (ForInStep γ)} :
    letI : ForIn' m (Iter (α := α) β) β _ := Iter.instForIn'
    ForIn'.forIn' it init f = ForIn'.forIn' it.toList init (fun out h acc => f out (Iter.mem_toList_iff_isPlausibleIndirectOutput.mp h) acc) := by
  simp only [forIn'_toList]
  congr

theorem Iter.forIn_toList {α β : Type w} [Iterator α Id β]
    [Finite α Id] {m : Type x → Type x'} [Monad m] [LawfulMonad m]
    [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    {γ : Type x} {it : Iter (α := α) β} {init : γ}
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
    · simp only [ForIn.forIn] at ihy
      simp [ihy h]
  · rename_i it' h
    simp only [bind_pure_comp]
    rw [ihs h]
  · simp

theorem Iter.foldM_eq_forIn {α β : Type w} {γ : Type x} [Iterator α Id β] [Finite α Id]
    {m : Type x → Type x'} [Monad m] [IteratorLoop α Id m] {f : γ → β → m γ}
    {init : γ} {it : Iter (α := α) β} :
    it.foldM (init := init) f = ForIn.forIn it init (fun x acc => ForInStep.yield <$> f acc x) :=
  (rfl)

theorem Iter.foldM_eq_foldM_toIterM {α β : Type w} [Iterator α Id β]
    [Finite α Id] {m : Type w → Type w''} [Monad m] [LawfulMonad m]
    [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    {γ : Type w} {it : Iter (α := α) β} {init : γ} {f : γ → β → m γ} :
    it.foldM (init := init) f = it.toIterM.foldM (init := init) f := by
  simp [foldM_eq_forIn, IterM.foldM_eq_forIn, forIn_eq_forIn_toIterM]

theorem Iter.forIn_yield_eq_foldM {α β : Type w} {γ : Type x} {δ : Type x} [Iterator α Id β]
    [Finite α Id] {m : Type x → Type x'} [Monad m] [LawfulMonad m] [IteratorLoop α Id m]
    [LawfulIteratorLoop α Id m] {f : β → γ → m δ} {g : β → γ → δ → γ} {init : γ}
    {it : Iter (α := α) β} :
    ForIn.forIn (m := m) it init (fun c b => (fun d => .yield (g c b d)) <$> f c b) =
      it.foldM (m := m) (fun b c => g c b <$> f c b) init := by
  simp [Iter.foldM_eq_forIn]

theorem Iter.foldM_eq_match_step {α β : Type w} {γ : Type x} [Iterator α Id β] [Finite α Id]
    {m : Type x → Type x'} [Monad m] [LawfulMonad m] [IteratorLoop α Id m]
    [LawfulIteratorLoop α Id m] {f : γ → β → m γ} {init : γ} {it : Iter (α := α) β} :
    it.foldM (init := init) f = (do
      match it.step with
      | .yield it' out _ => it'.foldM (init := ← f init out) f
      | .skip it' _ => it'.foldM (init := init) f
      | .done _ => return init) := by
  rw [Iter.foldM_eq_forIn, Iter.forIn_eq_match_step]
  generalize it.step = step
  cases step using PlausibleIterStep.casesOn <;> simp [foldM_eq_forIn]

theorem Iter.foldlM_toList {α β : Type w} {γ : Type x} [Iterator α Id β] [Finite α Id]
    {m : Type x → Type x'} [Monad m] [LawfulMonad m] [IteratorLoop α Id m]
    [LawfulIteratorLoop α Id m] [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    {f : γ → β → m γ} {init : γ} {it : Iter (α := α) β} :
    it.toList.foldlM (init := init) f = it.foldM (init := init) f := by
  rw [Iter.foldM_eq_forIn, ← Iter.forIn_toList]
  simp only [List.forIn_yield_eq_foldlM, id_map']

theorem IterM.forIn_eq_foldM {α β : Type w} [Iterator α Id β]
    [Finite α Id] {m : Type x → Type x'} [Monad m] [LawfulMonad m]
    [IteratorLoop α Id m] [LawfulIteratorLoop α Id m]
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    {γ : Type x} {it : Iter (α := α) β} {init : γ}
    {f : β → γ → m (ForInStep γ)} :
    forIn it init f = ForInStep.value <$>
      it.foldM (fun c b => match c with
        | .yield c => f b c
        | .done c => pure (.done c)) (ForInStep.yield init) := by
  simp only [← Iter.forIn_toList, List.forIn_eq_foldlM, ← Iter.foldlM_toList]; rfl

theorem Iter.fold_eq_forIn {α β : Type w} {γ : Type x} [Iterator α Id β]
    [Finite α Id] [IteratorLoop α Id Id] {f : γ → β → γ} {init : γ} {it : Iter (α := α) β} :
    it.fold (init := init) f =
      (ForIn.forIn (m := Id) it init (fun x acc => pure (ForInStep.yield (f acc x)))).run := by
  rfl

theorem Iter.fold_eq_foldM {α β : Type w} {γ : Type x} [Iterator α Id β]
    [Finite α Id] [IteratorLoop α Id Id] {f : γ → β → γ} {init : γ} {it : Iter (α := α) β} :
    it.fold (init := init) f = (it.foldM (m := Id) (init := init) (pure <| f · ·)).run := by
  simp [foldM_eq_forIn, fold_eq_forIn]

@[simp]
theorem Iter.forIn_pure_yield_eq_fold {α β : Type w} {γ : Type x} [Iterator α Id β]
    [Finite α Id] [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id] {f : β → γ → γ} {init : γ}
    {it : Iter (α := α) β} :
    ForIn.forIn (m := Id) it init (fun c b => pure (.yield (f c b))) =
      pure (it.fold (fun b c => f c b) init) := by
  simp only [fold_eq_forIn]
  rfl

theorem Iter.fold_eq_match_step {α β : Type w} {γ : Type x} [Iterator α Id β] [Finite α Id]
    [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id] {f : γ → β → γ} {init : γ} {it : Iter (α := α) β} :
    it.fold (init := init) f = (match it.step with
      | .yield it' out _ => it'.fold (init := f init out) f
      | .skip it' _ => it'.fold (init := init) f
      | .done _ => init) := by
  rw [fold_eq_foldM, foldM_eq_match_step]
  simp only [fold_eq_foldM]
  generalize it.step = step
  cases step using PlausibleIterStep.casesOn <;> simp

@[simp]
theorem Iter.foldl_toList {α β : Type w} {γ : Type x} [Iterator α Id β] [Finite α Id]
    [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    {f : γ → β → γ} {init : γ} {it : Iter (α := α) β} :
    it.toList.foldl (init := init) f = it.fold (init := init) f := by
  rw [fold_eq_foldM, List.foldl_eq_foldlM, ← Iter.foldlM_toList]

@[simp]
theorem Iter.size_toArray_eq_size {α β : Type w} [Iterator α Id β] [Finite α Id]
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    [IteratorSize α Id] [LawfulIteratorSize α]
    {it : Iter (α := α) β} :
    it.toArray.size = it.size := by
  simp only [toArray_eq_toArray_toIterM, LawfulIteratorCollect.toArray_eq]
  simp [← toArray_eq_toArray_toIterM, LawfulIteratorSize.size_eq_size_toArray]

@[simp]
theorem Iter.length_toList_eq_size {α β : Type w} [Iterator α Id β] [Finite α Id]
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    [IteratorSize α Id] [LawfulIteratorSize α]
    {it : Iter (α := α) β} :
    it.toList.length = it.size := by
  rw [← toList_toArray, Array.length_toList, size_toArray_eq_size]

@[simp]
theorem Iter.length_toListRev_eq_size {α β : Type w} [Iterator α Id β] [Finite α Id]
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    [IteratorSize α Id] [LawfulIteratorSize α]
    {it : Iter (α := α) β} :
    it.toListRev.length = it.size := by
  rw [toListRev_eq, List.length_reverse, length_toList_eq_size]

end Std.Iterators
