/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Gallicchio
-/
module

prelude
public import Init.NotationExtra
import Init.Data.Fin.Lemmas
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Sublist
import Init.Data.List.TakeDrop
public import Init.Data.List.FinRange
public import Init.Data.List.Find

public section

/-!
# Lemmas about `List.Pairwise`
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

set_option linter.listVariables false in
/-- Given a list `is` of monotonically increasing indices into `l`, getting each index
  produces a sublist of `l`.  -/
theorem map_getElem_sublist {l : List α} {is : List (Fin l.length)} (h : is.Pairwise (· < ·)) :
    is.map (l[·]) <+ l := by
  suffices ∀ j l', l' = l.drop j → (∀ i ∈ is, j ≤ i) → map (l[·]) is <+ l'
    from this 0 l (by simp) (by simp)
  rintro j l' rfl his
  induction is generalizing j with
  | nil => simp
  | cons hd tl IH =>
    simp only [Fin.getElem_fin, map_cons]
    have := IH h.of_cons (hd+1) (pairwise_cons.mp h).1
    specialize his hd (.head _)
    have := (drop_eq_getElem_cons ..).symm ▸ this.cons_cons (get l hd)
    have := Sublist.append (nil_sublist (take hd l |>.drop j)) this
    rwa [nil_append, ← (drop_append_of_le_length ?_), take_append_drop] at this
    simp [Nat.min_eq_left (Nat.le_of_lt hd.isLt), his]

set_option linter.listVariables false in
/-- Given a sublist `l' <+ l`, there exists an increasing list of indices `is` such that
  `l' = is.map fun i => l[i]`. -/
theorem sublist_eq_map_getElem {l l' : List α} (h : l' <+ l) : ∃ is : List (Fin l.length),
    l' = is.map (l[·]) ∧ is.Pairwise (· < ·) := by
  induction h with
  | slnil => exact ⟨[], by simp⟩
  | cons _ _ IH =>
    let ⟨is, IH⟩ := IH
    refine ⟨is.map (·.succ), ?_⟩
    set_option backward.isDefEq.respectTransparency false in
    simpa [Function.comp_def, pairwise_map]
  | cons_cons _ _ IH =>
    rcases IH with ⟨is,IH⟩
    refine ⟨⟨0, by simp [Nat.zero_lt_succ]⟩ :: is.map (·.succ), ?_⟩
    set_option backward.isDefEq.respectTransparency false in
    simp [Function.comp_def, pairwise_map, IH, ← get_eq_getElem, get_cons_zero, get_cons_succ']

/-- The list `List.finRange n` is strictly increasing. -/
theorem pairwise_lt_finRange (n : Nat) : Pairwise (· < ·) (finRange n) := by
  rw [pairwise_iff_getElem]
  intro i j hi hj hlt
  simp only [getElem_finRange]
  exact hlt

/-- The list `List.finRange n` is increasing. -/
theorem pairwise_le_finRange (n : Nat) : Pairwise (· ≤ ·) (finRange n) := by
  rw [pairwise_iff_getElem]
  intro i j hi hj hlt
  simp only [getElem_finRange]
  exact Fin.le_of_lt hlt

/-- The list `List.finRange n` has no duplicate entries. -/
theorem nodup_finRange (n : Nat) : (finRange n).Nodup :=
  (pairwise_lt_finRange n).imp Fin.ne_of_lt

/-- In a list with no duplicates, `idxOf` recovers the index of the element at
each position. -/
@[simp]
theorem Nodup.idxOf_getElem [BEq α] [LawfulBEq α] {xs : List α} (H : Nodup xs)
    (i : Nat) (h : i < xs.length) : idxOf xs[i] xs = i := by
  induction xs generalizing i with
  | nil => exact absurd h (Nat.not_lt_zero i)
  | cons a l ih =>
    rw [nodup_cons] at H
    match i with
    | 0 => rw [getElem_cons_zero, idxOf_cons_self]
    | j + 1 =>
      have hj : j < l.length := Nat.lt_of_succ_lt_succ h
      have hne : (a == l[j]) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun hc => H.1 (hc ▸ getElem_mem hj)
      rw [getElem_cons_succ, idxOf_cons, hne, cond_false, ih H.2 j hj]

grind_pattern Nodup.idxOf_getElem => Nodup xs, idxOf (xs[i]'h) xs

end List
