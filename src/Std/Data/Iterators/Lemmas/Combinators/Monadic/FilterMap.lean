/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Combinators.Monadic.FilterMap
import Std.Data.Iterators.Lemmas.Consumers.Monadic

namespace Std.Iterators

section Step

variable {α : Type w} {m : Type w → Type w'} {β : Type w} {β' : Type w}
  [Iterator α m β] (it : IterM (α := α) m β) [Monad m]
  (f : β → PostconditionT m (Option β'))

theorem IterM.step_filterMapWithProof [LawfulMonad m] :
  (it.filterMapWithProof f).step = (do
    match ← it.step with
    | .yield it' out h => do
      match ← (f out).operation with
      | ⟨none, h'⟩ =>
        pure <| .skip (it'.filterMapWithProof f) (.yieldNone (out := out) h h')
      | ⟨some out', h'⟩ =>
        pure <| .yield (it'.filterMapWithProof f) out' (.yieldSome (out := out) h h')
    | .skip it' h =>
      pure <| .skip (it'.filterMapWithProof f) (.skip h)
    | .done h =>
      pure <| .done (.done h)) := by
  apply bind_congr
  intro step
  match step with
  | .yield it' out h =>
    simp
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem IterM.step_filterMap [LawfulMonad m] {f : β → Option β'} :
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
  simp only [IterM.filterMap, step_filterMapWithProof, pure]
  apply bind_congr
  intro step
  split
  · simp only [pure_bind]
    split <;> split <;> simp_all
  · simp
  · simp

theorem IterM.step_mapWithProof [LawfulMonad m] {f : β → PostconditionT m β'} :
  (it.mapWithProof f).step = (do
    match ← it.step with
    | .yield it' out h => do
      let out' ← (f out).operation
      pure <| .yield (it'.mapWithProof f) out'.1 (.yieldSome h ⟨out', rfl⟩)
    | .skip it' h =>
      pure <| .skip (it'.mapWithProof f) (.skip h)
    | .done h =>
      pure <| .done (.done h)) := by
  change (it.filterMapWithProof _).step = _
  rw [step_filterMapWithProof]
  apply bind_congr
  intro step
  split
  · simp only [PostconditionT.operation_map, bind_map_left, bind_pure_comp]
    rfl
  · rfl
  · rfl

theorem IterM.step_map [LawfulMonad m] {f : β → β'} :
  (it.map f).step = (do
    match ← it.step with
    | .yield it' out h =>
      let out' := f out
      pure <| .yield (it'.map f) out' (.yieldSome h ⟨⟨out', rfl⟩, rfl⟩)
    | .skip it' h =>
      pure <| .skip (it'.map f) (.skip h)
    | .done h => pure <| .done (.done h)) := by
  simp only [map, IterM.step_mapWithProof]
  apply bind_congr
  intro step
  split
  · simp
  · rfl
  · rfl

theorem IterM.step_filter [LawfulMonad m] {f : β → Bool} :
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

variable {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''} {m : Type w → Type x}
    [Monad n] [Monad o] [Iterator α m β] {lift : ⦃δ : Type w⦄ -> m δ → n δ} {f : β → PostconditionT n γ}

instance [LawfulMonad n] [IteratorCollect α m o]
    [LawfulIteratorCollect α m o] :
    LawfulIteratorCollect (Map α m n lift f) n o where
  finite := inferInstance
  lawful := by
    intro γ
    ext f it
    have : it = it.inner.inner.mapWithProof _ := rfl
    generalize it.inner.inner = it at *
    cases this
    simp only [IteratorCollect.toArrayMapped]
    rw [LawfulIteratorCollect.lawful]
    induction it using IterM.induct with | step it ih_yield ih_skip =>
    rw [IterM.DefaultConsumers.toArrayMapped_of_step]
    rw [IterM.DefaultConsumers.toArrayMapped_of_step]
    simp only [IterM.step_mapWithProof, bind_assoc]
    apply bind_congr
    intro step
    split
    · simp only [bind_pure_comp, bind_map_left, ← ih_yield ‹_›]
      rfl
    · simp only [bind_pure_comp, pure_bind, ← ih_skip ‹_›]
      rfl
    · simp

end Lawful

section Congruence

def IterM.Morphisms.filterMapWithProofCongrRight {α : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {β : Type w} [Iterator α m β] {γ : Type w} {f g : β → PostconditionT m (Option γ)} (h : f = g) :
    Morphism (FilterMap α f) (FilterMap α g) m := by
  exact h ▸ Morphism.id _ m

-- TODO: upstream from Mathlib.Logic.Basic? Note that this lemma is more general
theorem Eq.rec_eq_cast {α : Sort _} {a : α} {motive : (a' : α) → a = a' → Sort _} (x : motive a rfl) {a' : α} (h : a = a') :
    (Eq.rec x h : motive a' h) = cast (by cases h; rfl) x := by
  cases h; rfl

-- TODO: upstream from Mathlib.Logic.Basic?
theorem eq_cast_iff_heq : a = cast e b ↔ HEq a b := by cases e; simp

private theorem Eq.apply_rec' {α : Type u} {β : α → Type v} {γ : α → Type w} {a a' : α} (h : a = a')
    (f : ∀ a, β a → γ a) (x : β a) : f a' (h ▸ x) = h ▸ (f a x) := by
  cases h
  simp

def IterM.Morphisms.mapToFilterMap (α : Type w) (m : Type w → Type w') [Monad m] [LawfulMonad m]
    {β : Type w} [Iterator α m β]
    {γ : Type w} (f : β → γ) :
    Morphism (β := γ) (Map α (fun x => (pure (f x) : PostconditionT m _)))
      (FilterMap α (fun x => (pure (some (f x)) : PostconditionT m _)) (γ := γ)) m := by
  apply IterM.Morphism.copy
  case f => exact fun it => it.inner.inner.filterMapWithProof _
  case φ => exact filterMapWithProofCongrRight (α := α) (m := m) (by simp)
  case h =>
    ext it
    simp only [filterMapWithProofCongrRight, Eq.apply_rec' _ fun (a : _) (ψ : Morphism _ _ m) => ψ.map it,
      Morphism.id]
    rw [Eq.rec_eq_cast, eq_cast_iff_heq]
    rw (occs := [2]) [(rfl : it = it.inner.inner.filterMapWithProof _)]
    apply HEq.congrArg (fun f => it.inner.inner.filterMapWithProof f)
    simp

end Congruence

section ToList

variable {α : Type w} {m : Type w → Type w'} {β : Type w} {β' : Type w}
  [Iterator α m β] (it : IterM (α := α) m β) [Monad m]

theorem IterM.toList_filterMap {α : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m] {β : Type w}
    [Iterator α m β] [IteratorCollect α m] [LawfulIteratorCollect α m] {f : β → Option β'}
    (it : IterM (α := α) m β) :
    (it.filterMap f).toList = (fun x => x.filterMap f) <$> it.toList := by
  induction it using IterM.induct
  rename_i it ihy ihs
  rw [IterM.toList_of_step, IterM.toList_of_step]
  simp
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
  · simp
    apply ihs
    assumption
  · simp

theorem IterM.toList_map {α : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m] {β : Type w}
    [Iterator α m β] [IteratorCollect α m] [LawfulIteratorCollect α m] {f : β → β'}
    (it : IterM (α := α) m β) :
    (it.map f).toList = (fun x => x.map f) <$> it.toList := by
  rw [(IterM.Morphisms.mapToFilterMap α m f).toList_eq]
  change (it.filterMap _).toList = _
  rw [toList_filterMap]
  change (fun x => x.filterMap (some ∘ f)) <$> it.toList = _
  rw [List.filterMap_eq_map]

theorem IterM.toList_filter {α : Type w} {m : Type w → Type w'} [Monad m] [LawfulMonad m]
    {β : Type w} [Iterator α m β] [IteratorCollect α m] [LawfulIteratorCollect α m] {f : β → Bool}
    {it : IterM (α := α) m β} :
    (it.filter f).toList = List.filter f <$> it.toList := by
  simp only [filter, toList_filterMap, ← List.filterMap_eq_filter]
  rfl

end ToList

end Std.Iterators
