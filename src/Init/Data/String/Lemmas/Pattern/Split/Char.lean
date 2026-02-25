/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Slice
import Init.Data.String.Lemmas.Pattern.Basic
import Init.Data.Iterators.Lemmas.Combinators.FilterMap
import Init.Data.String.Lemmas.Pattern.Split.Basic
import Init.Data.String.Lemmas.Pattern.Char
import Init.Data.String.Termination
import Init.ByCases
import Init.Data.Order.Lemmas
import Init.Data.String.OrderInstances
import Init.Data.String.Lemmas.Order
import Init.Data.String.Lemmas.Basic

namespace List

def splitOnPAndPrepend (p : α → Bool) : List α → List α → List (List α)
  | [], acc => [acc.reverse]
  | a :: t, acc => if p a then acc.reverse :: splitOnPAndPrepend p t [] else splitOnPAndPrepend p t (a::acc)

@[simp]
theorem splitOnPAndPrepend_nil_left {p : α → Bool} {acc : List α} :
    splitOnPAndPrepend p [] acc = [acc.reverse] := by
  simp [splitOnPAndPrepend]

/--
Split a list at every element satisfying a predicate. The separators are not in the result.
```
[1, 1, 2, 3, 2, 4, 4].splitOnP (· == 2) = [[1, 1], [3], [4, 4]]
```
-/
def splitOnP (p : α → Bool) (l : List α) : List (List α) :=
  splitOnPAndPrepend p l []

@[simp]
theorem splitOnPAndPrepend_nil_right {p : α → Bool} {l : List α} : splitOnPAndPrepend p l [] = splitOnP p l := (rfl)

theorem splitOnPAndPrepend_cons_pos {p : α → Bool} {a : α} {l acc : List α} (h : p a) :
    splitOnPAndPrepend p (a :: l) acc = acc.reverse :: splitOnP p l := by
  simp [splitOnPAndPrepend, h]

theorem splitOnPAndPrepend_cons_neg {p : α → Bool} {a : α} {l acc : List α} (h : p a = false) :
    splitOnPAndPrepend p (a :: l) acc = splitOnPAndPrepend p l (a :: acc) := by
  simp [splitOnPAndPrepend, h]

@[simp]
theorem splitOnP_nil {p : α → Bool} : [].splitOnP p = [[]] := by
  simp [splitOnP, splitOnPAndPrepend]


end List

namespace String.Slice

@[simp]
theorem copy_slice_self {s : Slice} {p : s.Pos} : (s.slice p p (Std.le_refl _)).copy = "" := by
  simp [copy_eq_empty_iff, ← Slice.startPos_eq_endPos_iff, ← Pos.ofSlice_inj]

@[simp]
theorem Pos.ne_next {s : Slice} {p : s.Pos} {h : p ≠ s.endPos} : p ≠ p.next h :=
  Std.ne_of_lt (by simp)

theorem Pos.get_eq_get_ofSlice {s : Slice} {p q : s.Pos} {h} {r : (s.slice p q h).Pos} {h'} :
    r.get h' = (Pos.ofSlice r).get (by sorry) := sorry

#check Pos.ofSliceFrom_lt_ofSliceFrom_iff

theorem Pos.ofSlice_next {s : Slice} {p₀ p₁ : s.Pos} {h₀} {p : (s.slice p₀ p₁ h₀).Pos} {h} :
    Pos.ofSlice (p.next h) = (Pos.ofSlice p).next (sorry) := by
  sorry

@[simp]
theorem push_empty {c : Char} : "".push c = String.singleton c := rfl

theorem copy_slice_of_lt {s : Slice} {p q : s.Pos} (h : p < q) :
    (s.slice p q (Std.le_of_lt h)).copy = String.singleton (p.get (Pos.ne_endPos_of_lt h)) ++
      (s.slice (p.next (Pos.ne_endPos_of_lt h)) q (by simpa)).copy := by
  have hsp := (s.slice p q (Std.le_of_lt h)).splits_startPos
  obtain ⟨t₂, ht⟩ := hsp.exists_eq_singleton_append (by simpa [← Pos.ofSlice_inj] using Std.ne_of_lt h)
  have := (ht ▸ hsp).next.eq_right (Slice.Pos.splits _)
  simpa [Pos.ofSlice_next, this, Pos.get_eq_get_ofSlice] using ht

@[simp]
theorem copy_slice_next {s : Slice} {p : s.Pos} {h} :
    (s.slice p (p.next h) (by simp)).copy = String.singleton (p.get h) := by
  rw [copy_slice_of_lt (by simp), copy_slice_self, String.append_empty]

@[simp]
theorem Pos.ofSlice_slice {s : Slice} {p₀ p₁ p : s.Pos} {h₁ h₂} :
    Pos.ofSlice (p.slice p₀ p₁ h₁ h₂) = p := sorry

theorem splits_slice {s : Slice} {p₀ p₁ : s.Pos} (h) (p : (s.slice p₀ p₁ h).Pos) :
    p.Splits (s.slice p₀ (Pos.ofSlice p) Pos.le_ofSlice).copy (s.slice (Pos.ofSlice p) p₁ Pos.ofSlice_le).copy := by
  simpa using p.splits

open Pattern.Model Pattern.Model.Char

theorem toStringList_splitToSubslice_char {s : Slice} {c : Char} :
    (s.splitToSubslice c).toStringList = (s.copy.toList.splitOnP (· == c)).map String.ofList := by
  simp [Std.Iter.toList_map, Pattern.toList_splitToSubslice_eq_modelSplit]
  suffices ∀ (f p : s.Pos) (hle : f ≤ p) (t₁ t₂ : String),
      p.Splits t₁ t₂ → (Pattern.Model.split c f p hle).map ToString.toString =
        (t₂.toList.splitOnPAndPrepend (· == c) (s.subslice f p hle).copy.toList.reverse).map String.ofList by
    simpa using this s.startPos s.startPos (Std.le_refl _) "" s.copy
  intro f p hle t₁ t₂ hp
  induction p using Pos.next_induction generalizing f t₁ t₂ with
  | next p h ih =>
    obtain ⟨t₂, rfl⟩ := hp.exists_eq_singleton_append h
    by_cases hpc : p.get h = c
    · simp only [split_eq_of_isLongestMatchAt (isLongestMatchAt_of_get_eq hpc), List.map_cons,
        Subslice.toString_eq', toSlice_subslice, ih _ (Std.le_refl _) _ _ hp.next, Subslice.copy_eq,
        copy_slice_self, toList_empty, List.reverse_nil, List.splitOnPAndPrepend_nil_right,
        toList_append, toList_singleton, List.cons_append, List.nil_append]
      rw [List.splitOnPAndPrepend_cons_pos (by simpa)]
      simp
    · rw [split_eq_next_of_not_matchesAt h (not_matchesAt_of_get_ne hpc)]
      simp
      rw [ih _ _ _ _ hp.next, List.splitOnPAndPrepend_cons_neg (by simpa)]
      have := (splits_slice (Std.le_trans hle (by simp)) (p.slice f (p.next h) hle (by simp))).eq_append
      simp at this
      simp [this]
  | endPos => simp_all

theorem toStringList_split_char {s : Slice} {c : Char} :
    (s.split c).toStringList = (s.copy.toList.splitOnP (· == c)).map String.ofList := sorry

end String.Slice
