/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic

namespace Array

def qpartition (as : Array α) (lt : α → α → Bool) (lo hi : Nat) : Nat × Array α :=
  let s := as.size
  have hs: as.size = s := rfl

  let hi := if hi < s then hi else s - 1

  if hlh: lo ≥ hi then (lo, as) else
  have hlh: lo < hi := Nat.gt_of_not_le hlh

  have h0s: s ≠ 0 := by
    dsimp only [hi] at hlh
    split at hlh
    case isTrue h =>
      exact Nat.not_eq_zero_of_lt h
    case isFalse h =>
      apply Nat.ne_of_gt
      apply Nat.zero_lt_of_lt
      exact Nat.add_lt_of_lt_sub hlh

  have hhs: hi < s := by
    dsimp only [hi]
    split
    · assumption
    · apply Nat.sub_one_lt
      exact h0s

  -- we need this since otherwise loop doesn't capture hi, but rather what it unfolds to
  have ⟨hi, hlh, hhs⟩: (hi: Nat) ×' (lo < hi) ×' (hi < s) := ⟨hi, hlh, hhs⟩

  have hls: lo < s := Nat.lt_trans hlh hhs

  let mid := (lo + hi) / 2

  have hms: mid < s := by
    apply Nat.div_lt_of_lt_mul
    rw [Nat.two_mul]
    exact Nat.add_lt_add hls hhs

  let b := lt as[mid] as[lo]
  let as := if b then as.swap ⟨lo, hs ▸ hls⟩ ⟨mid, hs ▸ hms⟩ else as
  have hs: as.size = s := by dsimp only [as]; split; all_goals simp_all only [Array.size_swap]

  -- we need let b since otherwise the split tactic fails
  let b := lt as[hi] as[lo]
  let as  := if b then as.swap ⟨lo, hs ▸ hls⟩ ⟨hi, hs ▸ hhs⟩  else as
  have hs: as.size = s := by dsimp only [as]; split; all_goals simp_all only [Array.size_swap]

  let b := lt as[mid] as[hi]
  let as := if b then as.swap ⟨mid, hs ▸ hms⟩ ⟨hi, hs ▸ hhs⟩ else as
  have hs: as.size = s := by dsimp only [as]; split; all_goals simp_all only [Array.size_swap]

  let pivot := as[hi]

  let rec loop (as : Array α) (i j : Nat) (hij: i ≤ j) (hjh: j ≤ hi) (hhs: hi < as.size):=
    let s := as.size
    have hs: as.size = s := rfl

    have his: i < s := Nat.lt_of_le_of_lt hij (Nat.lt_of_le_of_lt hjh hhs)

    if hjh : j < hi then
      have hjs: j < s := Nat.lt_trans hjh hhs

      if lt as[j] pivot then
        let as := as.swap ⟨i, hs ▸ his⟩ ⟨j, hs ▸ hjs⟩
        have hs: as.size = s := by simp_all only [as, Array.size_swap]

        have hij: i + 1 ≤ j + 1 := Nat.add_le_add_right hij 1

        loop as (i+1) (j+1) hij hjh (hs ▸ hhs)
      else
        have hij: i ≤ j + 1 := Nat.le_add_right_of_le hij

        loop as i (j+1) hij hjh (hs ▸ hhs)
    else
      let as := as.swap ⟨i, hs ▸ his⟩ ⟨hi, hs ▸ hhs⟩
      (i, as)

  have hlh: lo ≤ hi := Nat.le_of_succ_le hlh
  have hll: lo ≤ lo := Nat.le_refl lo

  loop as lo lo hll hlh (hs ▸ hhs)

theorem i_le_qpartition_loop_fst (lt: α → α → Bool) {hi: Nat} (pivot: α) {as: Array α} {i: Nat} {j: Nat}
    (hij: i ≤ j) (hjh: j ≤ hi) (hhs: hi < as.size):
  i ≤ (qpartition.loop lt hi pivot as i j hij hjh hhs).1 := by
  unfold qpartition.loop
  -- the split tactic fails
  by_cases hjh: j < hi
  all_goals simp only [hjh, ↓reduceDIte]
  · split
    · apply Nat.le_of_succ_le
      apply i_le_qpartition_loop_fst
    · apply i_le_qpartition_loop_fst
  · apply Nat.le_refl

theorem lo_le_qpartition_fst (as: Array α) (lt: α → α → Bool) (lo hi: Nat):
    lo ≤ (qpartition as lt lo hi).1 := by
  unfold qpartition
  -- the split tactic fails
  by_cases hlh: lo ≥ (if hi < as.size then hi else as.size - 1)
  all_goals simp only [hlh, ↓reduceDIte]
  · apply Nat.le_refl
  · apply i_le_qpartition_loop_fst

@[inline] def qsort (as : Array α) (lt : α → α → Bool) (low := 0) (high := as.size - 1) : Array α :=
  let rec @[specialize] sort (as : Array α) (low high : Nat) :=
    if hlh: low < high then
      let p := qpartition as lt low high
      let mid := p.1
      let as  := p.2
      if hmh: mid >= high then as
      else
        let as := sort as low mid
        sort as (mid+1) high
    else as
  termination_by high - low
  decreasing_by
    · apply Nat.sub_lt_sub_right
      · apply lo_le_qpartition_fst
      · exact Nat.gt_of_not_le hmh
    · apply Nat.sub_lt_sub_left
      · exact hlh
      · apply Nat.lt_succ_of_le
        apply lo_le_qpartition_fst

  sort as low high
end Array
