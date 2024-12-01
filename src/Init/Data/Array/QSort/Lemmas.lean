/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.QSort.Basic
import Init.Data.Vector.Lemmas
import Init.Data.Array.Perm

namespace Array

open List
#print qpartition.loop
theorem qpartition_loop_perm {n} (as : Vector α n) (lt : α → α → Bool) (lo hi : Nat)
    {hhi} {ilo} {jh} :
    (qpartition.loop lt lo hi hhi pivot as i j ilo jh w).2.toArray ~ as.toArray := by
  unfold qpartition.loop
  split
  · split
    · refine Perm.trans (qpartition_loop_perm ..) ?_

      simp only [Vector.toArray_swap, toList_swap, Vector.getElem_toArray]

theorem qpartition_perm {n} (as : Vector α n) (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) :
    (qpartition as lt lo hi hlo hhi).2.toList ~ as.toList := by
  simp [qpartition]

theorem qpartition_spec₁ {n} (as : Vector α n) (lt : α → α → Bool) (lo hi : Nat)
    (hlo : lo < n := by omega) (hhi : hi < n := by omega) :
    let ⟨⟨mid, h₁, h₂⟩, as⟩ := qpartition as lt lo hi hlo hhi
    (∀ i, (h₁ : i ≤ lo) → (h₂ : i < mid) → lt as[i] as[mid]) := by
  sorry
  simp [qpartition]

end Array
