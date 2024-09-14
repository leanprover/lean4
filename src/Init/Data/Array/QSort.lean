/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic
import Init.Data.Nat.Mod

namespace Array

@[specialize] def qpartition (as : Array α) (lt : α → α → Bool) (low high : Nat)
    (hlh: low ≤ high := by omega) (hhs: high < as.size := by omega): Nat × Array α :=
  let s := as.size
  have hs: as.size = s := rfl

  have hls: low < s := Nat.lt_of_le_of_lt hlh hhs

  let mid := (low + high) / 2

  have hms: mid < s := by
    apply Nat.div_lt_of_lt_mul
    rw [Nat.two_mul]
    exact Nat.add_lt_add hls hhs

  let as := if lt (as[mid]'(hs ▸ hms)) (as[low]'(hs ▸ hls)) then as.swap ⟨low, hs ▸ hls⟩ ⟨mid, hs ▸ hms⟩ else as
  have hs: as.size = s := by dsimp only [as]; split; all_goals simp_all only [Array.size_swap]

  let as := if lt (as[high]'(hs ▸ hhs)) (as[low]'(hs ▸ hls)) then as.swap ⟨low, hs ▸ hls⟩ ⟨high, hs ▸ hhs⟩  else as
  have hs: as.size = s := by dsimp only [as]; split; all_goals simp_all only [Array.size_swap]

  let as := if lt (as[mid]'(hs ▸ hms)) (as[high]'(hs ▸ hhs)) then as.swap ⟨mid, hs ▸ hms⟩ ⟨high, hs ▸ hhs⟩ else as
  have hs: as.size = s := by dsimp only [as]; split; all_goals simp_all only [Array.size_swap]

  let pivot := as[high]'(hs ▸ hhs)

  let rec @[specialize] loop (as : Array α) (i j : Nat) (hij: i ≤ j) (hjh: j ≤ high) (hhs: high < as.size):=
    let s := as.size
    have hs: as.size = s := rfl

    have his: i < s := Nat.lt_of_le_of_lt hij (Nat.lt_of_le_of_lt hjh hhs)

    if hjh : j < high then
      have hjs: j < s := Nat.lt_trans hjh hhs

      if lt (as[j]'(hs ▸ hjs)) pivot then
        let as := as.swap ⟨i, hs ▸ his⟩ ⟨j, hs ▸ hjs⟩
        have hs: as.size = s := by simp_all only [as, Array.size_swap]

        have hij: i + 1 ≤ j + 1 := Nat.add_le_add_right hij 1

        loop as (i+1) (j+1) hij hjh (hs ▸ hhs)
      else
        have hij: i ≤ j + 1 := Nat.le_add_right_of_le hij

        loop as i (j+1) hij hjh (hs ▸ hhs)
    else
      let as := as.swap ⟨i, hs ▸ his⟩ ⟨high, hs ▸ hhs⟩
      (i, as)

  have hll: low ≤ low := Nat.le_refl low

  loop as low low hll hlh (hs ▸ hhs)

theorem i_le_fst_qpartition_loop (lt: α → α → Bool) {high: Nat} (pivot: α) {as: Array α} {i: Nat} {j: Nat}
    (hij: i ≤ j) (hjh: j ≤ high) (hhs: high < as.size):
    i ≤ (qpartition.loop lt high pivot as i j hij hjh hhs).1 := by
  unfold qpartition.loop
  dsimp only
  split
  · split
    · apply Nat.le_of_succ_le
      apply i_le_fst_qpartition_loop
    · apply i_le_fst_qpartition_loop
  · apply Nat.le_refl

theorem fst_qpartition_loop_le_high (lt: α → α → Bool) (high: Nat) (pivot: α) (as: Array α) (i: Nat) (j: Nat)
    (hij: i ≤ j) (hjh: j ≤ high) (hhs: high < as.size):
    (qpartition.loop lt high pivot as i j hij hjh hhs).1 ≤ high := by
  unfold qpartition.loop
  dsimp only
  split
  · split
    · apply fst_qpartition_loop_le_high
    · apply fst_qpartition_loop_le_high
  · exact Nat.le_trans hij hjh

theorem size_snd_qpartition_loop (lt: α → α → Bool) {high: Nat} (pivot: α) {as: Array α} {i: Nat} {j: Nat}
    (hij: i ≤ j) (hjh: j ≤ high) (hhs: high < as.size):
    (qpartition.loop lt high pivot as i j hij hjh hhs).2.size = as.size := by
  unfold qpartition.loop
  dsimp only
  split
  · split
    · rw [size_snd_qpartition_loop]
      apply size_swap
    · apply size_snd_qpartition_loop
  · apply size_swap

theorem low_le_fst_qpartition (as: Array α) (lt: α → α → Bool) (low high: Nat)
    (hlh: low ≤ high) (hhs: high < as.size):
    low ≤ (qpartition as lt low high hlh hhs).1 := by
  apply i_le_fst_qpartition_loop

theorem fst_qpartition_le_high (as: Array α) (lt: α → α → Bool) (low high: Nat)
    (hlh: low ≤ high) (hhs: high < as.size):
    (qpartition as lt low high hlh hhs).1 ≤ high := by
  apply fst_qpartition_loop_le_high

@[simp] theorem size_snd_qpartition (as: Array α) (lt: α → α → Bool) (low high: Nat)
    (hlh: low ≤ high) (hhs: high < as.size):
    (qpartition as lt low high hlh hhs).2.size = as.size := by
  simp only [qpartition, size_snd_qpartition_loop, size_ite, size_swap, ite_self]

@[inline] def qsort (as : Array α) (lt : α → α → Bool) (low := 0) (high := as.size - 1)
    (hlh: low ≤ high := by omega) (hhs: low < high → high < as.size := by omega) : Array α :=

  let rec @[specialize] sort (as : Array α) (low high : Nat)
      (hlh: low ≤ high) (hhs: low < high → high < as.size): {as': Array α // as'.size = as.size} :=
    let s := as.size
    have hs: as.size = s := rfl
    if hlh': low < high then
      have hhs := hhs hlh'

      let p := qpartition as lt low high hlh (hs ▸ hhs)
      let mid := p.1
      let as  := p.2
      have hs: as.size = s := by
        simp only [as, p, size_snd_qpartition, hs]

      if hmh: mid >= high then ⟨as, hs⟩
      else
        have hms: mid < s := by
          apply Nat.lt_of_le_of_lt ?_ hhs
          apply fst_qpartition_le_high

        have hlm: low ≤ mid := by
          apply low_le_fst_qpartition

        have hmh: mid + 1 ≤ high := Nat.succ_le_of_lt (Nat.gt_of_not_le hmh)

        let ⟨as, hs'⟩ := sort as low mid hlm (λ _ ↦ hs ▸ hms)
        have hs: as.size = s := by rw [← hs, hs']

        let ⟨as, hs'⟩ := sort as (mid+1) high hmh (λ _ ↦ hs ▸ hhs)
        have hs: as.size = s := by rw [← hs, hs']

        ⟨as, hs⟩
    else ⟨as, hs⟩
  termination_by high - low
  decreasing_by
    · apply Nat.sub_lt_sub_right
      · apply low_le_fst_qpartition
      · exact hmh
    · apply Nat.sub_lt_sub_left
      · exact hlh'
      · apply Nat.lt_succ_of_le
        apply low_le_fst_qpartition

  (sort as low high hlh hhs).1

@[simp]
theorem size_qsort (as : Array α) (lt : α → α → Bool) (low := 0) (high := as.size - 1)
    (hlh: low ≤ high := by omega) (hhs: low < high → high < as.size := by omega):
    (qsort as lt low high hlh hhs).size = as.size := by
  unfold qsort
  exact (qsort.sort lt as low high hlh hhs).2

def qsort_nats (as : Array Nat) :=
  qsort as (· < · )

end Array
