/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Slice
import Init.Data.String.Lemmas.Pattern.Find.Basic
import Init.Data.String.Lemmas.Pattern.Pred
import Init.Data.String.Lemmas.Basic
import Init.Data.String.Lemmas.Order
import Init.Data.String.Termination
import Init.Data.String.Lemmas.Iterate
import Init.Grind

namespace String.Slice

theorem find?_bool_eq_some_iff {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    s.find? p = some pos ↔
      ∃ h, p (pos.get h) ∧ ∀ pos', (h' : pos' < pos) → p (pos'.get (Pos.ne_endPos_of_lt h')) = false := by
  grind [Pattern.Model.find?_eq_some_iff, Pattern.Model.CharPred.matchesAt_iff]

theorem find?_prop_eq_some_iff {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    s.find? p = some pos ↔
      ∃ h, p (pos.get h) ∧ ∀ pos', (h' : pos' < pos) → ¬ p (pos'.get (Pos.ne_endPos_of_lt h')) := by
  grind [Pattern.Model.find?_eq_some_iff, Pattern.Model.CharPred.Decidable.matchesAt_iff]

@[simp]
theorem contains_bool_eq {p : Char → Bool} {s : Slice} : s.contains p = s.copy.toList.any p := by
  rw [Bool.eq_iff_iff, Pattern.Model.contains_eq_true_iff]
  simp only [Pattern.Model.CharPred.matchesAt_iff, ne_eq, List.any_eq_true,
    mem_toList_copy_iff_exists_get]
  exact ⟨fun ⟨pos, h, hp⟩ => ⟨_, ⟨_, _, rfl⟩, hp⟩, fun ⟨_, ⟨p, h, h'⟩, hp⟩ => ⟨p, h, h' ▸ hp⟩⟩

@[simp]
theorem contains_prop_eq {p : Char → Prop} [DecidablePred p] {s : Slice} :
    s.contains p = s.copy.toList.any p := by
  rw [Bool.eq_iff_iff, Pattern.Model.contains_eq_true_iff]
  simp only [Pattern.Model.CharPred.Decidable.matchesAt_iff, ne_eq, List.any_eq_true,
    mem_toList_copy_iff_exists_get, decide_eq_true_eq]
  exact ⟨fun ⟨pos, h, hp⟩ => ⟨_, ⟨_, _, rfl⟩, hp⟩, fun ⟨_, ⟨p, h, h'⟩, hp⟩ => ⟨p, h, h' ▸ hp⟩⟩

end String.Slice
