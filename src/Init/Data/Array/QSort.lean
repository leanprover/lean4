/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic
import Init.Data.Nat.Mod

namespace Array

@[inline] def qsort (as : Array α) (lt : α → α → Bool) (low := 0) (high := as.size - 1)
    (hlh: low ≤ high := by omega) (hhs: low < high → high < as.size := by omega) : Array α :=

  let rec @[specialize] sort (as : Array α) (low high : Nat)
      (hlh: low ≤ high) (hhs: low < high → high < as.size): {as': Array α // as'.size = as.size} :=
    let s := as.size
    have hs: as.size = s := rfl
    if hlh': low >= high then
      ⟨as, hs⟩
    else
      have hlh': low < high := Nat.gt_of_not_le hlh'
      have hhs := hhs hlh'

      let s := as.size
      have hs: as.size = s := rfl

      have hls: low < s := Nat.lt_of_le_of_lt hlh hhs

      let i := (low + high) / 2

      have hms: i < s := by
        apply Nat.div_lt_of_lt_mul
        rw [Nat.two_mul]
        exact Nat.add_lt_add hls hhs

      let as := if lt (as[i]'(hs ▸ hms)) (as[low]'(hs ▸ hls)) then as.swap ⟨low, hs ▸ hls⟩ ⟨i, hs ▸ hms⟩ else as
      have hs: as.size = s := by dsimp only [as]; split; all_goals simp_all only [Array.size_swap]

      let as := if lt (as[high]'(hs ▸ hhs)) (as[low]'(hs ▸ hls)) then as.swap ⟨low, hs ▸ hls⟩ ⟨high, hs ▸ hhs⟩  else as
      have hs: as.size = s := by dsimp only [as]; split; all_goals simp_all only [Array.size_swap]

      let as := if lt (as[i]'(hs ▸ hms)) (as[high]'(hs ▸ hhs)) then as.swap ⟨i, hs ▸ hms⟩ ⟨high, hs ▸ hhs⟩ else as
      have hs: as.size = s := by dsimp only [as]; split; all_goals simp_all only [Array.size_swap]

      let pivot := as[high]'(hs ▸ hhs)

      let rec @[specialize] loop (as : Array α) (i j : Nat) (hli: low ≤ i) (hij: i ≤ j) (hjh: j ≤ high) (hhs: high < as.size): {as': Array α // as'.size = as.size}:=
        let s := as.size
        have hs: as.size = s := rfl
        have his: i < s := Nat.lt_of_le_of_lt hij (Nat.lt_of_le_of_lt hjh hhs)

        if hjh' : j < high then
          have hjs: j < s := Nat.lt_trans hjh' hhs

          if lt (as[j]'(hs ▸ hjs)) pivot then
            let as := as.swap ⟨i, hs ▸ his⟩ ⟨j, hs ▸ hjs⟩
            have hs: as.size = s := by simp_all only [as, Array.size_swap]

            have hij: i + 1 ≤ j + 1 := Nat.add_le_add_right hij 1
            have hli: low ≤ i + 1 := Nat.le_add_right_of_le hli

            let ⟨as, hs'⟩ := loop as (i+1) (j+1) hli hij hjh' (hs ▸ hhs)
            have hs: as.size = s := by rw [← hs, hs']

            ⟨as, hs⟩
          else
            have hij: i ≤ j + 1 := Nat.le_add_right_of_le hij

            let ⟨as, hs'⟩ := loop as i (j+1) hli hij hjh' (hs ▸ hhs)
            have hs: as.size = s := by rw [← hs, hs']

            ⟨as, hs⟩
        else if hih: i >= high then
          -- this can only happen if low == high assuming lt is antisymmetric
          -- that's because i == j == high implies that all x in [low, high) are less than the pivot as[high]
          -- in particular, this means that if mid != high, as[mid] is less than as[high], which is impossible,
          -- because we swap them in that case, so that a[mid] >= a[high]
          -- hence, mid = high, which implies (low + high) / 2 = high, which implies that low = high or
          -- low = high + 1, the latter of which is impossible because low <= high; hence, low == high

            ⟨as, hs⟩
          else
            let as := as.swap ⟨i, hs ▸ his⟩ ⟨high, hs ▸ hhs⟩
            have hs: as.size = s := by simp_all only [as, Array.size_swap]

            have hih: i < high := Nat.gt_of_not_le hih
            have his: i < s := Nat.lt_trans hih hhs

            let ⟨as, hs'⟩ := sort as low i hli (λ _ ↦ hs ▸ his)
            have hs: as.size = s := by rw [← hs, hs']

            let ⟨as, hs'⟩ := sort as (i+1) high hih (λ _ ↦ hs ▸ hhs)
            have hs: as.size = s := by rw [← hs, hs']

            ⟨as, hs⟩
            termination_by (high - low, 0, high - j)

      have hll: low ≤ low := Nat.le_refl low

      let ⟨as, hs'⟩ := loop as low low hll hll hlh (hs ▸ hhs)
      have hs: as.size = s := by rw [← hs, hs']

      ⟨as, hs⟩
      termination_by (high - low, 1, 0)

  (sort as low high hlh hhs).1

@[simp] theorem size_qsort (as : Array α) (lt : α → α → Bool) (low := 0) (high := as.size - 1)
    (hlh: low ≤ high := by omega) (hhs: low < high → high < as.size := by omega):
    (qsort as lt low high hlh hhs).size = as.size := by
  unfold qsort
  exact (qsort.sort lt as low high hlh hhs).2

end Array
