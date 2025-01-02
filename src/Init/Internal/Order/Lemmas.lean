/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude

import Init.Data.List.Control
import Init.Data.Array.Basic
import Init.Internal.Order.Basic

namespace Lean.Order

section monad

variable {m : Type u → Type v} [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m]
variable {α β : Type u}
variable {γ : Type w} [PartialOrder γ]

theorem monotone_option_bindM (f : γ → α → m (Option β)) (xs : Option α) (hmono : monotone f) :
    monotone (fun x => xs.bindM (f x)) := by
  cases xs with
  | none => apply monotone_const
  | some x =>
    apply monotone_bind
    · apply monotone_apply
      apply hmono
    · apply monotone_const

theorem monotone_option_mapM (f : γ → α → m β) (xs : Option α) (hmono : monotone f) :
    monotone (fun x => xs.mapM (f x)) := by
  cases xs with
  | none => apply monotone_const
  | some x =>
    apply monotone_bind
    · apply monotone_apply
      apply hmono
    · apply monotone_const

theorem monotone_option_elimM (a : γ → m (Option α)) (n : γ → m β) (s : γ → α → m β)
    (hmono₁ : monotone a) (hmono₂ : monotone n) (hmono₃ : monotone s) :
    monotone (fun x => Option.elimM (a x) (n x) (s x)) := by
  apply monotone_bind
  · apply hmono₁
  · apply monotone_of_monotone_apply
    intro o
    cases o
    case none => apply hmono₂
    case some y =>
      dsimp only [Option.elim]
      apply monotone_apply
      apply hmono₃

omit [MonoBind m] in
theorem monotone_option_getDM (o : Option α) (y : γ → m α) (hmono : monotone y) :
    monotone (fun x => o.getDM (y x)) := by
  cases o
  · apply hmono
  · apply monotone_const

theorem monotone_list_mapM (f : γ → α → m β) (xs : List α) (hmono : monotone f) :
    monotone (fun x => xs.mapM (f x)) := by
  cases xs with
  | nil => apply monotone_const
  | cons _ xs =>
    apply monotone_bind
    · apply monotone_apply
      apply hmono
    · apply monotone_of_monotone_apply
      intro y
      dsimp
      generalize [y] = ys
      induction xs generalizing ys with
      | nil => apply monotone_const
      | cons _ _ ih =>
        apply monotone_bind
        · apply monotone_apply
          apply hmono
        · apply monotone_of_monotone_apply
          intro y
          apply ih

theorem monotone_list_forM (f : γ → α → m PUnit) (xs : List α) (hmono : monotone f) :
    monotone (fun x => xs.forM (f x)) := by
  induction xs with
  | nil => apply monotone_const
  | cons _ _ ih =>
    apply monotone_bind
    · apply monotone_apply
      apply hmono
    · apply monotone_of_monotone_apply
      intro y
      apply ih

theorem monotone_list_filterAuxM
  {m : Type → Type v} [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] {α : Type}
  (f : γ → α → m Bool) (xs acc : List α) (hmono : monotone f) :
    monotone (fun x => xs.filterAuxM (f x) acc) := by
  induction xs generalizing acc with
  | nil => apply monotone_const
  | cons _ _ ih =>
    apply monotone_bind
    · apply monotone_apply
      apply hmono
    · apply monotone_of_monotone_apply
      intro y
      apply ih

theorem monotone_list_filterM
    {m : Type → Type v} [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] {α : Type}
    (f : γ → α → m Bool) (xs : List α) (hmono : monotone f) :
    monotone (fun x => xs.filterM (f x)) := by
  apply monotone_bind
  · exact monotone_list_filterAuxM f xs [] hmono
  · apply monotone_const

theorem monotone_list_filterRevM
    {m : Type → Type v} [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] {α : Type}
    (f : γ → α → m Bool) (xs : List α) (hmono : monotone f) :
    monotone (fun x => xs.filterRevM (f x)) := by
  exact monotone_list_filterAuxM f xs.reverse [] hmono

theorem monotone_list_foldlM
    (f : γ → β → α → m β) (init : β) (xs : List α) (hmono : monotone f) :
    monotone (fun x => xs.foldlM (f x) (init := init)) := by
  induction xs generalizing init with
  | nil => apply monotone_const
  | cons _ _ ih =>
    apply monotone_bind
    · apply monotone_apply
      apply monotone_apply
      apply hmono
    · apply monotone_of_monotone_apply
      intro y
      apply ih

theorem monotone_list_foldrM
    (f : γ → α → β → m β) (init : β) (xs : List α) (hmono : monotone f) :
    monotone (fun x => xs.foldrM (f x) (init := init)) := by
  apply monotone_list_foldlM
  apply monotone_of_monotone_apply
  intro s
  apply monotone_of_monotone_apply
  intro a
  apply monotone_apply (a := s)
  apply monotone_apply (a := a)
  apply hmono

theorem monotone_list_anyM
    {m : Type → Type v} [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] {α : Type}
    (f : γ → α → m Bool) (xs : List α) (hmono : monotone f) :
    monotone (fun x => xs.anyM (f x)) := by
  induction xs with
  | nil => apply monotone_const
  | cons _ _ ih =>
    apply monotone_bind
    · apply monotone_apply
      apply hmono
    · apply monotone_of_monotone_apply
      intro y
      cases y
      · apply ih
      · apply monotone_const

theorem monotone_list_allM
    {m : Type → Type v} [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] {α : Type}
    (f : γ → α → m Bool) (xs : List α) (hmono : monotone f) :
    monotone (fun x => xs.allM (f x)) := by
  induction xs with
  | nil => apply monotone_const
  | cons _ _ ih =>
    apply monotone_bind
    · apply monotone_apply
      apply hmono
    · apply monotone_of_monotone_apply
      intro y
      cases y
      · apply monotone_const
      · apply ih

theorem monotone_list_findM?
    {m : Type → Type v} [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] {α : Type}
    (f : γ → α → m Bool) (xs : List α) (hmono : monotone f) :
    monotone (fun x => xs.findM? (f x)) := by
  induction xs with
  | nil => apply monotone_const
  | cons _ _ ih =>
    apply monotone_bind
    · apply monotone_apply
      apply hmono
    · apply monotone_of_monotone_apply
      intro y
      cases y
      · apply ih
      · apply monotone_const

theorem monotone_list_findSomeM?
    (f : γ → α → m (Option β)) (xs : List α) (hmono : monotone f) :
    monotone (fun x => xs.findSomeM? (f x)) := by
  induction xs with
  | nil => apply monotone_const
  | cons _ _ ih =>
    apply monotone_bind
    · apply monotone_apply
      apply hmono
    · apply monotone_of_monotone_apply
      intro y
      cases y
      · apply ih
      · apply monotone_const

theorem monotone_array_mapFinIdxM (xs : Array α) (f : γ → Fin xs.size → α → m β) (hmono : monotone f) :
    monotone (fun x => xs.mapFinIdxM (f x)) := by
  suffices
    ∀ i j (h : i + j = xs.size) r, monotone (fun x => Array.mapFinIdxM.map xs (f x) i j h r) by
    apply this
  intros i j h r
  induction i, j, h, r using Array.mapFinIdxM.map.induct xs
  case case1 =>
    apply monotone_const
  case case2 ih =>
    apply monotone_bind
    · dsimp
      apply monotone_apply
      apply monotone_apply
      apply hmono
    · intro y
      apply monotone_of_monotone_apply
      apply ih

end monad

end Lean.Order
