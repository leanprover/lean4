/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

prelude

import Init.Data.List.Control
import Init.Data.Array.Basic
import Init.Internal.Order.Basic

/-!

This file contains monotonicity lemmas for higher-order monadic operations (e.g. `mapM`) in the
standard library. This allows recursive definitions using `partial_fixpoint` to use nested
recursion.

Ideally, every higher-order monadic function in the standard library has a lemma here. At the time
of writing, this file covers functions from

* Init/Data/Option/Basic.lean
* Init/Data/List/Control.lean
* Init/Data/Array/Basic.lean

in the order of their appearance there. No automation to check the exhaustiveness exists yet.

The lemma statements are written manually, but follow a predictable scheme, and could be automated.
Likewise, the proofs are written very naively. Most of them could be handled by a tactic like
`monotonicity` (extended to make use of local hypotheses).
-/

namespace Lean.Order

open Lean.Order

variable {m : Type u → Type v} [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m]
variable {α β : Type u}
variable {γ : Type w} [PartialOrder γ]

@[partial_fixpoint_monotone]
theorem Functor.monotone_map [LawfulMonad m] (f : γ → m α) (g : α → β) (hmono : monotone f) :
    monotone (fun x => g <$> f x) := by
  simp only [← LawfulMonad.bind_pure_comp ]
  apply monotone_bind _ _ _ hmono
  apply monotone_const

@[partial_fixpoint_monotone]
theorem Seq.monotone_seq [LawfulMonad m] (f : γ → m α) (g : γ → m (α → β))
  (hmono₁ : monotone g) (hmono₂ : monotone f) :
    monotone (fun x => g x <*> f x) := by
  simp only [← LawfulMonad.bind_map ]
  apply monotone_bind
  · assumption
  · apply monotone_of_monotone_apply
    intro y
    apply Functor.monotone_map
    assumption

@[partial_fixpoint_monotone]
theorem SeqLeft.monotone_seqLeft [LawfulMonad m] (f : γ → m α) (g : γ → m β)
  (hmono₁ : monotone g) (hmono₂ : monotone f) :
    monotone (fun x => g x <* f x) := by
  simp only [seqLeft_eq]
  apply Seq.monotone_seq
  · apply Functor.monotone_map
    assumption
  · assumption

@[partial_fixpoint_monotone]
theorem SeqRight.monotone_seqRight [LawfulMonad m] (f : γ → m α) (g : γ → m β)
  (hmono₁ : monotone g) (hmono₂ : monotone f) :
    monotone (fun x => g x *> f x) := by
  simp only [seqRight_eq]
  apply Seq.monotone_seq
  · apply Functor.monotone_map
    assumption
  · assumption

namespace Option

@[partial_fixpoint_monotone]
theorem monotone_bindM (f : γ → α → m (Option β)) (xs : Option α) (hmono : monotone f) :
    monotone (fun x => xs.bindM (f x)) := by
  cases xs with
  | none => apply monotone_const
  | some x =>
    apply monotone_bind
    · apply monotone_apply
      apply hmono
    · apply monotone_const

@[partial_fixpoint_monotone]
theorem monotone_mapM (f : γ → α → m β) (xs : Option α) (hmono : monotone f) :
    monotone (fun x => xs.mapM (f x)) := by
  cases xs with
  | none => apply monotone_const
  | some x =>
    apply monotone_bind
    · apply monotone_apply
      apply hmono
    · apply monotone_const

@[partial_fixpoint_monotone]
theorem monotone_elimM (a : γ → m (Option α)) (n : γ → m β) (s : γ → α → m β)
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
@[partial_fixpoint_monotone]
theorem monotone_getDM (o : Option α) (y : γ → m α) (hmono : monotone y) :
    monotone (fun x => o.getDM (y x)) := by
  cases o
  · apply hmono
  · apply monotone_const

end Option


namespace List

@[partial_fixpoint_monotone]
theorem monotone_mapM (f : γ → α → m β) (xs : List α) (hmono : monotone f) :
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

@[partial_fixpoint_monotone]
theorem monotone_forM (f : γ → α → m PUnit) (xs : List α) (hmono : monotone f) :
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

@[partial_fixpoint_monotone]
theorem monotone_filterAuxM
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

@[partial_fixpoint_monotone]
theorem monotone_filterM
    {m : Type → Type v} [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] {α : Type}
    (f : γ → α → m Bool) (xs : List α) (hmono : monotone f) :
    monotone (fun x => xs.filterM (f x)) := by
  apply monotone_bind
  · exact monotone_filterAuxM f xs [] hmono
  · apply monotone_const

@[partial_fixpoint_monotone]
theorem monotone_filterRevM
    {m : Type → Type v} [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] {α : Type}
    (f : γ → α → m Bool) (xs : List α) (hmono : monotone f) :
    monotone (fun x => xs.filterRevM (f x)) := by
  exact monotone_filterAuxM f xs.reverse [] hmono

@[partial_fixpoint_monotone]
theorem monotone_foldlM
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

@[partial_fixpoint_monotone]
theorem monotone_foldrM
    (f : γ → α → β → m β) (init : β) (xs : List α) (hmono : monotone f) :
    monotone (fun x => xs.foldrM (f x) (init := init)) := by
  apply monotone_foldlM
  apply monotone_of_monotone_apply
  intro s
  apply monotone_of_monotone_apply
  intro a
  apply monotone_apply (a := s)
  apply monotone_apply (a := a)
  apply hmono

@[partial_fixpoint_monotone]
theorem monotone_anyM
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

@[partial_fixpoint_monotone]
theorem monotone_allM
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

@[partial_fixpoint_monotone]
theorem monotone_findM?
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

@[partial_fixpoint_monotone]
theorem monotone_findSomeM?
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

@[partial_fixpoint_monotone]
theorem monotone_forIn'_loop {α : Type uu}
    (as : List α) (f : γ → (a : α) → a ∈ as → β → m (ForInStep β)) (as' : List α) (b : β)
    (p : Exists (fun bs => bs ++ as' = as)) (hmono : monotone f) :
    monotone (fun x => List.forIn'.loop as (f x) as' b p) := by
  induction as' generalizing b with
  | nil => apply monotone_const
  | cons a as' ih =>
    apply monotone_bind
    · apply monotone_apply
      apply monotone_apply
      apply monotone_apply
      apply hmono
    · apply monotone_of_monotone_apply
      intro y
      cases y with
      | done => apply monotone_const
      | yield => apply ih

@[partial_fixpoint_monotone]
theorem monotone_forIn' {α : Type uu}
    (as : List α) (init : β) (f : γ → (a : α) → a ∈ as → β → m (ForInStep β)) (hmono : monotone f) :
    monotone (fun x => forIn' as init (f x)) := by
  apply monotone_forIn'_loop
  apply hmono

@[partial_fixpoint_monotone]
theorem monotone_forIn {α : Type uu}
    (as : List α) (init : β) (f : γ → (a : α) → β → m (ForInStep β)) (hmono : monotone f) :
    monotone (fun x => forIn as init (f x)) := by
  apply monotone_forIn' as init _
  apply monotone_of_monotone_apply
  intro y
  apply monotone_of_monotone_apply
  intro p
  apply monotone_apply (a := y)
  apply hmono

end List

namespace Array

@[partial_fixpoint_monotone]
theorem monotone_modifyM (a : Array α) (i : Nat) (f : γ → α → m α) (hmono : monotone f) :
    monotone (fun x => a.modifyM i (f x)) := by
  unfold Array.modifyM
  split
  · apply monotone_bind
    · apply monotone_apply
      apply hmono
    · apply monotone_const
  · apply monotone_const

@[partial_fixpoint_monotone]
theorem monotone_forIn'_loop {α : Type uu}
    (as : Array α) (f : γ → (a : α) → a ∈ as → β → m (ForInStep β)) (i : Nat) (h : i ≤ as.size)
    (b : β) (hmono : monotone f) :
    monotone (fun x => Array.forIn'.loop as (f x) i h b) := by
  induction i, h, b using Array.forIn'.loop.induct with
  | case1 => apply monotone_const
  | case2 _ _ _ _ _ _ ih =>
    apply monotone_bind
    · apply monotone_apply
      apply monotone_apply
      apply monotone_apply
      apply hmono
    · apply monotone_of_monotone_apply
      intro y
      cases y with
      | done => apply monotone_const
      | yield => apply ih

@[partial_fixpoint_monotone]
theorem monotone_forIn' {α : Type uu}
    (as : Array α) (init : β) (f : γ → (a : α) → a ∈ as → β → m (ForInStep β)) (hmono : monotone f) :
    monotone (fun x => forIn' as init (f x)) := by
  apply monotone_forIn'_loop
  apply hmono


@[partial_fixpoint_monotone]
theorem monotone_forIn {α : Type uu}
    (as : Array α) (init : β) (f : γ → (a : α) → β → m (ForInStep β)) (hmono : monotone f) :
    monotone (fun x => forIn as init (f x)) := by
  apply monotone_forIn' as init _
  apply monotone_of_monotone_apply
  intro y
  apply monotone_of_monotone_apply
  intro p
  apply monotone_apply (a := y)
  apply hmono

@[partial_fixpoint_monotone]
theorem monotone_foldlM_loop
    (f : γ → β → α → m β) (xs : Array α) (stop : Nat) (h : stop ≤ xs.size) (i j : Nat) (b : β)
    (hmono : monotone f) : monotone (fun x => Array.foldlM.loop (f x) xs stop h i j b) := by
  induction i, j, b using Array.foldlM.loop.induct (h := h) with
  | case1 =>
    simp only [Array.foldlM.loop, ↓reduceDIte, *]
    apply monotone_const
  | case2 _ _ _ _ _ ih =>
    unfold Array.foldlM.loop
    simp only [↓reduceDIte, *]
    apply monotone_bind
    · apply monotone_apply
      apply monotone_apply
      apply hmono
    · apply monotone_of_monotone_apply
      apply ih
  | case3 =>
    simp only [Array.foldlM.loop, ↓reduceDIte, *]
    apply monotone_const

@[partial_fixpoint_monotone]
theorem monotone_foldlM
    (f : γ → β → α → m β) (init : β) (xs : Array α) (start stop : Nat) (hmono : monotone f) :
    monotone (fun x => xs.foldlM (f x) init start stop) := by
  unfold Array.foldlM
  split <;> apply monotone_foldlM_loop (hmono := hmono)

@[partial_fixpoint_monotone]
theorem monotone_foldrM_fold
    (f : γ → α → β → m β) (xs : Array α) (stop i : Nat) (h : i ≤ xs.size) (b : β)
    (hmono : monotone f) : monotone (fun x => Array.foldrM.fold (f x) xs stop i h b) := by
  induction i, h, b using Array.foldrM.fold.induct (stop := stop) with
  | case1 =>
    unfold Array.foldrM.fold
    simp only [↓reduceIte, *]
    apply monotone_const
  | case2  =>
    unfold Array.foldrM.fold
    simp only [↓reduceIte, *]
    apply monotone_const
  | case3 _ _ _ _ _ ih =>
    unfold Array.foldrM.fold
    simp only [reduceCtorEq, ↓reduceIte, *]
    apply monotone_bind
    · apply monotone_apply
      apply monotone_apply
      apply hmono
    · apply monotone_of_monotone_apply
      intro y
      apply ih

@[partial_fixpoint_monotone]
theorem monotone_foldrM
    (f : γ → α → β → m β) (init : β) (xs : Array α) (start stop : Nat) (hmono : monotone f) :
    monotone (fun x => xs.foldrM (f x) init start stop) := by
  unfold Array.foldrM
  split
  · split
    · apply monotone_foldrM_fold (hmono := hmono)
    · apply monotone_const
  · split
    · apply monotone_foldrM_fold (hmono := hmono)
    · apply monotone_const

@[partial_fixpoint_monotone]
theorem monotone_mapM (xs : Array α) (f : γ → α → m β) (hmono : monotone f) :
    monotone (fun x => xs.mapM (f x)) := by
  suffices ∀ i r, monotone (fun x => Array.mapM.map (f x) xs i r) by apply this
  intros i r
  induction i, r using Array.mapM.map.induct xs
  case case1 ih =>
    unfold Array.mapM.map
    simp only [↓reduceDIte, *]
    apply monotone_bind
    · apply monotone_apply
      apply hmono
    · intro y
      apply monotone_of_monotone_apply
      apply ih
  case case2 =>
    unfold Array.mapM.map
    simp only [↓reduceDIte, *]
    apply monotone_const

@[partial_fixpoint_monotone]
theorem monotone_mapFinIdxM (xs : Array α) (f : γ → (i : Nat) → α → i < xs.size → m β)
    (hmono : monotone f) : monotone (fun x => xs.mapFinIdxM (f x)) := by
  suffices ∀ i j (h : i + j = xs.size) r, monotone (fun x => Array.mapFinIdxM.map xs (f x) i j h r) by apply this
  intros i j h r
  induction i, j, h, r using Array.mapFinIdxM.map.induct xs
  case case1 =>
    apply monotone_const
  case case2 ih =>
    apply monotone_bind
    · dsimp
      apply monotone_apply
      apply monotone_apply
      apply monotone_apply
      apply hmono
    · intro y
      apply monotone_of_monotone_apply
      apply ih

@[partial_fixpoint_monotone]
theorem monotone_findSomeM?
    (f : γ → α → m (Option β)) (xs : Array α) (hmono : monotone f) :
    monotone (fun x => xs.findSomeM? (f x)) := by
  unfold Array.findSomeM?
  apply monotone_bind
  · apply monotone_forIn
    apply monotone_of_monotone_apply
    intro y
    apply monotone_of_monotone_apply
    intro r
    apply monotone_bind
    · apply monotone_apply
      apply hmono
    · apply monotone_const
  · apply monotone_const

@[partial_fixpoint_monotone]
theorem monotone_findM?
    {m : Type → Type} [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] {α : Type}
    (f : γ → α → m Bool) (xs : Array α) (hmono : monotone f) :
    monotone (fun x => xs.findM? (f x)) := by
  unfold Array.findM?
  apply monotone_bind
  · apply monotone_forIn
    apply monotone_of_monotone_apply
    intro y
    apply monotone_of_monotone_apply
    intro r
    apply monotone_bind
    · apply monotone_apply
      apply hmono
    · apply monotone_const
  · apply monotone_const

@[partial_fixpoint_monotone]
theorem monotone_findIdxM?
    {m : Type → Type v} [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] {α : Type u}
    (f : γ → α → m Bool) (xs : Array α) (hmono : monotone f) :
    monotone (fun x => xs.findIdxM? (f x)) := by
  unfold Array.findIdxM?
  apply monotone_bind
  · apply monotone_forIn
    apply monotone_of_monotone_apply
    intro y
    apply monotone_of_monotone_apply
    intro r
    apply monotone_bind
    · apply monotone_apply
      apply hmono
    · apply monotone_const
  · apply monotone_const

@[partial_fixpoint_monotone]
theorem monotone_anyM_loop
    {m : Type → Type v} [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] {α : Type u}
    (f : γ → α → m Bool) (xs : Array α) (stop : Nat) (h : stop ≤ xs.size) (j : Nat)
    (hmono : monotone f) : monotone (fun x => Array.anyM.loop (f x) xs stop h j) := by
  induction j using Array.anyM.loop.induct (h := h) with
  | case2 =>
    unfold Array.anyM.loop
    simp only [↓reduceDIte, *]
    apply monotone_const
  | case1 _ _ _ ih =>
    unfold Array.anyM.loop
    simp only [↓reduceDIte, *]
    apply monotone_bind
    · apply monotone_apply
      apply hmono
    · apply monotone_of_monotone_apply
      intro y
      split
      · apply monotone_const
      · apply ih

@[partial_fixpoint_monotone]
theorem monotone_anyM
    {m : Type → Type v} [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] {α : Type u}
    (f : γ → α → m Bool) (xs : Array α) (start stop : Nat) (hmono : monotone f) :
    monotone (fun x => xs.anyM (f x) start stop) := by
  unfold Array.anyM
  split
  · apply monotone_anyM_loop
    apply hmono
  · apply monotone_anyM_loop
    apply hmono

@[partial_fixpoint_monotone]
theorem monotone_allM
    {m : Type → Type v} [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] {α : Type u}
    (f : γ → α → m Bool) (xs : Array α) (start stop : Nat) (hmono : monotone f) :
    monotone (fun x => xs.allM (f x) start stop) := by
  unfold Array.allM
  apply monotone_bind
  · apply monotone_anyM
    apply monotone_of_monotone_apply
    intro y
    apply monotone_bind
    · apply monotone_apply
      apply hmono
    · apply monotone_const
  · apply monotone_const

@[partial_fixpoint_monotone]
theorem monotone_findSomeRevM?
    (f : γ → α → m (Option β)) (xs : Array α) (hmono : monotone f) :
    monotone (fun x => xs.findSomeRevM? (f x)) := by
  unfold Array.findSomeRevM?
  suffices ∀ i (h : i ≤ xs.size), monotone (fun x => Array.findSomeRevM?.find (f x) xs i h) by apply this
  intros i h
  induction i, h using Array.findSomeRevM?.find.induct with
  | case1 =>
    unfold Array.findSomeRevM?.find
    apply monotone_const
  | case2 _ _ _ ih =>
    unfold Array.findSomeRevM?.find
    apply monotone_bind
    · apply monotone_apply
      apply hmono
    · apply monotone_of_monotone_apply
      intro y
      cases y with
      | none => apply ih
      | some y => apply monotone_const

@[partial_fixpoint_monotone]
theorem monotone_findRevM?
    {m : Type → Type v} [Monad m] [∀ α, PartialOrder (m α)] [MonoBind m] {α : Type}
    (f : γ → α → m Bool) (xs : Array α) (hmono : monotone f) :
    monotone (fun x => xs.findRevM? (f x)) := by
  unfold Array.findRevM?
  apply monotone_findSomeRevM?
  apply monotone_of_monotone_apply
  intro y
  apply monotone_bind
  · apply monotone_apply
    apply hmono
  · apply monotone_const

@[partial_fixpoint_monotone]
theorem monotone_array_forM
    (f : γ → α → m PUnit) (xs : Array α) (start stop : Nat) (hmono : monotone f) :
    monotone (fun x => xs.forM (f x) start stop) := by
  unfold Array.forM
  apply monotone_foldlM
  apply monotone_of_monotone_apply
  intro y
  apply hmono

@[partial_fixpoint_monotone]
theorem monotone_array_forRevM
    (f : γ → α → m PUnit) (xs : Array α) (start stop : Nat) (hmono : monotone f) :
    monotone (fun x => xs.forRevM (f x) start stop) := by
  unfold Array.forRevM
  apply monotone_foldrM
  apply monotone_of_monotone_apply
  intro y
  apply monotone_of_monotone_apply
  intro z
  apply monotone_apply
  apply hmono

@[partial_fixpoint_monotone]
theorem monotone_flatMapM
    (f : γ → α → m (Array β)) (xs : Array α) (hmono : monotone f) :
    monotone (fun x => xs.flatMapM (f x)) := by
  unfold Array.flatMapM
  apply monotone_foldlM
  apply monotone_of_monotone_apply
  intro y
  apply monotone_of_monotone_apply
  intro z
  apply monotone_bind
  · apply monotone_apply
    apply hmono
  · apply monotone_const


@[partial_fixpoint_monotone]
theorem monotone_array_filterMapM
    (f : γ → α → m (Option β)) (xs : Array α) (hmono : monotone f) :
    monotone (fun x => xs.filterMapM (f x)) := by
  unfold Array.filterMapM
  apply monotone_foldlM
  apply monotone_of_monotone_apply
  intro y
  apply monotone_of_monotone_apply
  intro z
  apply monotone_bind
  · apply monotone_apply
    apply hmono
  · apply monotone_const

end Array

end Lean.Order
