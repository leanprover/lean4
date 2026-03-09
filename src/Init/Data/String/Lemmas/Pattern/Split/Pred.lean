/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Slice
public import Init.Data.String.Search
public import Init.Data.List.SplitOn.Basic
public import Init.Data.String.Lemmas.Pattern.Split.Basic
public import Init.Data.String.Lemmas.Pattern.Pred
import Init.Data.String.Termination
import all Init.Data.String.Lemmas.Pattern.Split.Basic
import Init.Data.Order.Lemmas
import Init.Data.Iterators.Lemmas.Combinators.FilterMap
import Init.Data.String.Lemmas.Pattern.Split.Basic
import Init.Data.String.Lemmas.Pattern.Pred
import Init.ByCases
import Init.Data.String.OrderInstances
import Init.Data.List.SplitOn.Lemmas
import Init.Data.String.Lemmas.Order

public section

namespace String.Slice

section

open Pattern.Model Pattern.Model.CharPred

theorem toList_splitToSubslice_bool {s : Slice} {p : Char → Bool} :
    (s.splitToSubslice p).toList.map (Slice.copy ∘ Subslice.toSlice) =
      (s.copy.toList.splitOnP p).map String.ofList := by
  simp only [Pattern.toList_splitToSubslice_eq_modelSplit]
  suffices ∀ (f pos : s.Pos) (hle : f ≤ pos) (t₁ t₂ : String),
      pos.Splits t₁ t₂ → (Pattern.Model.split p f pos hle).map (copy ∘ Subslice.toSlice) =
        (t₂.toList.splitOnPPrepend p (s.subslice f pos hle).copy.toList.reverse).map String.ofList by
    simpa using this s.startPos s.startPos (Std.le_refl _) "" s.copy
  intro f pos hle t₁ t₂ hp
  induction pos using Pos.next_induction generalizing f t₁ t₂ with
  | next pos h ih =>
    obtain ⟨t₂, rfl⟩ := hp.exists_eq_singleton_append h
    by_cases hpc : p (pos.get h)
    · simp [split_eq_of_isLongestMatchAt (isLongestMatchAt_of_get hpc),
        ih _ (Std.le_refl _) _ _ hp.next,
        List.splitOnPPrepend_cons_pos (p := p) hpc]
    · rw [Bool.not_eq_true] at hpc
      rw [split_eq_next_of_not_matchesAt h (not_matchesAt_of_get hpc)]
      simp only [toList_append, toList_singleton, List.cons_append, List.nil_append, Subslice.copy_eq]
      rw [ih _ _ _ _ hp.next, List.splitOnPPrepend_cons_neg (by simpa)]
      have := (splits_slice (Std.le_trans hle (by simp)) (pos.slice f (pos.next h) hle (by simp))).eq_append
      simp_all
  | endPos => simp_all

theorem toList_split_bool {s : Slice} {p : Char → Bool} :
    (s.split p).toList.map Slice.copy = (s.copy.toList.splitOnP p).map String.ofList := by
  simp [toList_split_eq_splitToSubslice, ← toList_splitToSubslice_bool]

end

section

open Pattern.Model Pattern.Model.CharPred.Decidable

theorem Pattern.Model.split_eq_split_decide {p : Char → Prop} [DecidablePred p] {s : Slice}
    (f curr : s.Pos) (hle : f ≤ curr) :
    Model.split p f curr hle = Model.split (decide <| p ·) f curr hle := by
  fun_induction Model.split p f curr hle with
  | case1 fr h => simp
  | case2 fr curr hle h pos h₁ h₂ ih =>
    conv => rhs; rw [Model.split]
    simp only [h, ↓reduceDIte]
    split <;> simp_all [matchAt?_eq_matchAt?_decide]
  | case3 fr curr hle h pos ih =>
    conv => rhs; rw [Model.split]
    simp only [h, ↓reduceDIte]
    split <;> simp_all [matchAt?_eq_matchAt?_decide]

theorem toList_splitToSubslice_prop {s : Slice} {p : Char → Prop} [DecidablePred p] :
    (s.splitToSubslice p).toList.map (Slice.copy ∘ Subslice.toSlice) =
      (s.copy.toList.splitOnP p).map String.ofList := by
  have : (s.splitToSubslice p).toList = (s.splitToSubslice (decide <| p ·)).toList := by
    simp only [Pattern.toList_splitToSubslice_eq_modelSplit, split_eq_split_decide]
  rw [this]
  exact toList_splitToSubslice_bool

theorem toList_split_prop {s : Slice} {p : Char → Prop} [DecidablePred p] :
    (s.split p).toList.map Slice.copy = (s.copy.toList.splitOnP p).map String.ofList := by
  simp [toList_split_eq_splitToSubslice, ← toList_splitToSubslice_prop]

end

end Slice

theorem toList_split_bool {s : String} {p : Char → Bool} :
    (s.split p).toList.map Slice.copy = (s.toList.splitOnP p).map String.ofList := by
  simp [split_eq_split_toSlice, Slice.toList_split_bool]

theorem toList_split_prop {s : String} {p : Char → Prop} [DecidablePred p] :
    (s.split p).toList.map Slice.copy = (s.toList.splitOnP p).map String.ofList := by
  simp [split_eq_split_toSlice, Slice.toList_split_prop]

end String
