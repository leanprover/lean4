/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Gallicchio
-/
prelude
import Init.Data.Fin.Lemmas
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise

/-!
# Lemmas about `List.Pairwise`
-/

-- set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

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
    have := (drop_eq_getElem_cons ..).symm ▸ this.cons₂ (get l hd)
    have := Sublist.append (nil_sublist (take hd l |>.drop j)) this
    rwa [nil_append, ← (drop_append_of_le_length ?_), take_append_drop] at this
    simp [Nat.min_eq_left (Nat.le_of_lt hd.isLt), his]

set_option linter.listVariables false in
@[deprecated map_getElem_sublist (since := "2024-07-30")]
theorem map_get_sublist {l : List α} {is : List (Fin l.length)} (h : is.Pairwise (·.val < ·.val)) :
    is.map (get l) <+ l := by
  simpa using map_getElem_sublist h

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
    simpa [Function.comp_def, pairwise_map]
  | cons₂ _ _ IH =>
    rcases IH with ⟨is,IH⟩
    refine ⟨⟨0, by simp [Nat.zero_lt_succ]⟩ :: is.map (·.succ), ?_⟩
    simp [Function.comp_def, pairwise_map, IH, ← get_eq_getElem, get_cons_zero, get_cons_succ']

set_option linter.listVariables false in
@[deprecated sublist_eq_map_getElem (since := "2024-07-30")]
theorem sublist_eq_map_get (h : l' <+ l) : ∃ is : List (Fin l.length),
    l' = map (get l) is ∧ is.Pairwise (· < ·) := by
  simpa using sublist_eq_map_getElem h

set_option linter.listVariables false in
theorem pairwise_iff_getElem : Pairwise R l ↔
    ∀ (i j : Nat) (_hi : i < l.length) (_hj : j < l.length) (_hij : i < j), R l[i] l[j] := by
  rw [pairwise_iff_forall_sublist]
  constructor <;> intro h
  · intros i j hi hj h'
    apply h
    simpa [h'] using map_getElem_sublist (is := [⟨i, hi⟩, ⟨j, hj⟩])
  · intros a b h'
    have ⟨is, h', hij⟩ := sublist_eq_map_getElem h'
    rcases is with ⟨⟩ | ⟨a', ⟨⟩ | ⟨b', ⟨⟩⟩⟩ <;> simp at h'
    rcases h' with ⟨rfl, rfl⟩
    apply h; simpa using hij

end List
