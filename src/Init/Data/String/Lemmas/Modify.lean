/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Modify
import all Init.Data.String.Modify
import Init.Data.String.Lemmas.Basic

/-!
# Lemmas for `Init.Data.String.Modify`

This file contains lemmas for the operations defined in `Init.Data.String.Modify`.

Note that `Init.Data.String.Modify` already proves a few lemmas which are needed immediately.
-/

public section

namespace String

/-- You might want to invoke `Pos.Splits.exists_eq_singleton_append` to be able to apply this. -/
theorem Pos.Splits.pastSet {s : String} {p : s.Pos} {t₁ t₂ : String}
    {c d : Char} (h : p.Splits t₁ (singleton c ++ t₂)) :
    (p.pastSet d h.ne_endPos_of_singleton).Splits (t₁ ++ singleton d) t₂ := by
  generalize h.ne_endPos_of_singleton = hp
  obtain ⟨rfl, rfl, rfl⟩ := by simpa using h.eq (p.splits_next_right hp)
  apply splits_pastSet

/-- You might want to invoke `Pos.Splits.exists_eq_singleton_append` to be able to apply this. -/
theorem Pos.Splits.pastModify {s : String} {p : s.Pos} {t₁ t₂ : String}
    {c : Char} (h : p.Splits t₁ (singleton c ++ t₂)) :
    (p.pastModify f h.ne_endPos_of_singleton).Splits
    (t₁ ++ singleton (f (p.get h.ne_endPos_of_singleton))) t₂ :=
  h.pastSet

theorem toList_mapAux {f : Char → Char} {s : String} {p : s.Pos}
    (h : p.Splits t₁ t₂) : (mapAux f s p).toList = t₁.toList ++ t₂.toList.map f := by
  fun_induction mapAux generalizing t₁ t₂ with
  | case1 s => simp_all
  | case2 s p hp ih =>
    obtain ⟨c, rfl⟩ := h.exists_eq_singleton_append hp
    simp [ih h.pastModify]

@[simp]
theorem toList_map {f : Char → Char} {s : String} : (s.map f).toList = s.toList.map f := by
  simp [map, toList_mapAux s.splits_startPos]

@[simp]
theorem map_eq_empty {f : Char → Char} {s : String} : s.map f = "" ↔ s = "" := by
  simp [← toList_eq_nil_iff]

end String
