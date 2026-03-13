/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.List.TakeDrop
public import Init.Data.List.Nat.TakeDrop
public import Init.Data.Range.Polymorphic.Basic
import Init.Data.Option.Lemmas
import Init.Omega
import Init.Data.Nat.Lemmas
import Init.ByCases
import Init.Data.Array.Lemmas

public section

variable {α : Type u} {as bs : List α} {i j k i' j' : Nat}

namespace List

@[simp]
theorem take_extract :
    (as.extract i j).take k = as.extract i (min (i + k) j) := by
  simp [extract_eq_drop_take', take_drop, take_take]

@[simp]
theorem extract_take :
    (as.take i).extract j k = as.extract j (min k i) := by
  simp [extract_eq_drop_take', take_take]

@[simp]
theorem drop_extract :
    (as.extract i j).drop k = as.extract (i + k) j := by
  simp [extract_eq_drop_take', drop_drop, drop_drop]

@[simp]
theorem extract_drop :
    (as.drop i).extract j k = as.extract (i + j) (i + k) := by
  simp [extract_eq_drop_take', take_drop]

@[simp]
theorem extract_extract :
    (as.extract i j).extract i' j' = as.extract (i + i') (min (i + j') j) := by
  simp [extract_eq_drop_take', take_drop, take_take]

grind_pattern extract_extract => (as.extract i j).extract i' j' where
  as =/= []

@[simp, grind =]
theorem length_extract :
    (as.extract i j).length = min j as.length - i := by
  simp [extract_eq_drop_take']

theorem length_extract_le_stop_sub_start :
    (as.extract i j).length ≤ j - i := by
  simp [extract_eq_drop_take']
  omega

theorem length_extract_le_length_sub_start :
    (as.extract i j).length ≤ as.length - i := by
  simp [extract_eq_drop_take']
  omega

theorem length_extract_of_le (h : j ≤ as.length) :
    (as.extract i j).length = j - i := by
  simp; omega

theorem length_extract_le_stop :
    (as.extract i j).length ≤ j := by
  simp [extract_eq_drop_take']
  omega

theorem length_extract_le_length :
    (as.extract i j).length ≤ as.length := by
  simp [extract_eq_drop_take']
  omega

theorem extract_eq_nil_of_stop_le_start (h : j ≤ i) :
    as.extract i j = [] := by
  simp [eq_nil_iff_length_eq_zero]; omega

theorem extract_eq_nil_of_length_le_start (h : as.length ≤ i) :
    as.extract i j = [] := by
  simp [eq_nil_iff_length_eq_zero]; omega

@[simp]
theorem extract_eq_nil_iff :
    as.extract i j = [] ↔ min j as.length ≤ i := by
  simp [extract_eq_drop_take']

theorem extract_eq_nil_of_le (h : min j as.length ≤ i) :
    as.extract i j = [] :=
  extract_eq_nil_iff.2 h

theorem lt_of_extract_ne_nil (h : as.extract i j ≠ []) :
    i < min j as.length := by
  simpa using h

@[simp]
theorem extract_length_left :
    as.extract as.length j = [] := by
  apply extract_eq_nil_of_length_le_start
  exact Nat.le_refl as.length

@[simp, grind =]
theorem extract_nil :
    ([] : List α).extract i j = [] := by
  simp [extract_eq_drop_take']

theorem extract_eq_nil_of_eq_nil (h : as = []) :
    as.extract i j = [] := by
  simp [h, List.extract_eq_drop_take']

theorem ne_nil_of_extract_ne_nil (h : as.extract i j ≠ []) :
    as ≠ [] :=
  mt extract_eq_nil_of_eq_nil h

@[simp]
theorem getElem?_extract_of_lt_stop (h : i + k < j) :
    (as.extract i j)[k]? = as[i + k]? := by
  simp only [extract_eq_drop_take', getElem?_drop]
  rw [getElem?_take_of_lt h]

theorem getElem?_extract_of_succ :
    (as.extract 0 (j + 1))[j]? = as[j]? := by
  simp

@[simp]
theorem getElem?_extract_eq_some_of_lt (h : i + k < min j as.length) :
    (as.extract i j)[k]? = some as[i + k] := by
  rw [getElem?_extract_of_lt_stop (by omega)]
  simp

theorem getElem?_extract_eq_none_iff :
   (as.extract i j)[k]? = none ↔ min j as.length ≤ i + k := by
  simp [extract_eq_drop_take']

theorem getElem?_extract_eq_dite :
    (as.extract i j)[k]? =
      if _ : i + k < min j as.length then some as[i + k] else none := by
  split <;> rename_i h
  · apply getElem?_extract_eq_some_of_lt h
  · simp; omega

theorem getElem?_extract_eq_ite :
    (as.extract i j)[k]? =
      if i + k < j then as[i + k]? else none := by
  simp [extract_eq_drop_take', getElem?_drop, getElem?_take]

theorem getElem?_extract :
    (as.extract i j)[k]? = if k < min j as.length - i then as[i + k]? else none := by
  simp [getElem?_extract_eq_dite, getElem_eq_getElem?_get, - get_getElem?, Nat.lt_sub_iff_add_lt',
    dite_eq_ite]

theorem head?_extract_eq_dite :
    (as.extract i j).head? =
      if _ : i < min j as.length then some as[i] else none := by
  simp [head?_eq_getElem?, getElem?_extract_eq_dite]

theorem head?_extract_eq_ite :
    (as.extract i j).head? = if i < j then as[i]? else none := by
  simp [head?_eq_getElem?, getElem?_extract_eq_ite]

theorem getElem_extract_aux (h : k < (as.extract i j).length) :
    i + k < as.length := by
  simp at h
  omega

@[simp, grind =]
theorem getElem_extract :
    (as.extract i j)[k]'h = as[i + k]'(getElem_extract_aux h) := by
  simp only [length_extract] at h
  simp [getElem_eq_getElem?_get, - get_getElem?, Option.get_inj]
  rw [getElem?_extract_of_lt_stop]
  omega

@[simp]
theorem getElem?_extract_of_lt (h : k < min j as.length - i) :
    (as.extract i j)[k]? = some (as[i + k]'(by omega)) := by
  simp [h]

theorem head_extract_aux (h : (as.extract i j) ≠ []) :
    i < as.length := by
  simp only [ne_eq, extract_eq_nil_iff, Nat.not_le] at h
  omega

@[simp]
theorem head_extract :
    (as.extract i j).head h = as[i]'(head_extract_aux h) := by
  simp [head_eq_getElem]

theorem getElem_eq_getElem_extract_aux (h : k < as.length)
    (hi : i ≤ k) (hj : k < j) :
    k - i < (as.extract i j).length := by
  simp; omega

theorem getElem_eq_getElem_extract {h} (hi : i ≤ k) (hj : k < j) :
    as[k]'h = (as.extract i j)[k - i]'(getElem_eq_getElem_extract_aux h hi hj) := by
  simp [getElem_extract, Nat.add_sub_cancel' hi]

@[congr]
theorem extract_congr
    (w : as = bs) (h : i = i') (h' : j = j') :
    as.extract i j = bs.extract i' j' := by
  subst w h h'
  rfl

theorem extract_eq_extract_self_of_eq
    (h : min i (min j as.length) = min i' (min j' as.length))
    (h' : min j as.length = min j' as.length) :
    as.extract i j = as.extract i' j' := by
  simp [extract_eq_drop_take']
  simp +singlePass only [take_eq_take_min]
  simp +singlePass only [drop_eq_drop_min]
  simp_all [Nat.min_assoc]

theorem extract_eq_extract_min :
    as.extract i j = as.extract (min i (min j as.length)) (min j as.length) := by
  apply extract_eq_extract_self_of_eq <;> simp

theorem extract_eq_extract_min_left :
    as.extract i j = as.extract (min i (min j as.length)) j := by
  apply extract_eq_extract_self_of_eq <;> simp

theorem extract_eq_extract_min_right :
    as.extract i j = as.extract i (min j as.length) := by
  apply extract_eq_extract_self_of_eq <;> simp

@[simp]
theorem extract_of_length_lt (h : as.length < j) :
    as.extract i j = as.extract i as.length := by
  rw [extract_eq_extract_min_right, Nat.min_eq_right (by omega)]

@[simp]
theorem extract_zero_length : as.extract 0 as.length = as := by
  apply List.ext_getElem <;> simp

theorem extract_length : as.extract i as.length = as.drop i := by
  simp [List.extract_eq_drop_take']

theorem extract_eq_drop_of_le (h : as.length ≤ j) :
    as.extract i j = as.drop i := by
  simp only [extract_eq_drop_take', drop_take]
  rw [take_of_length_le]
  simp; omega

theorem extract_zero_left :
    as.extract 0 j = as.take j := by
  simp [extract_eq_drop_take']

@[simp, grind =]
theorem extract_zero_right :
    as.extract i 0 = [] := by
  simp [extract_eq_drop_take']

theorem extract_succ_right (w : i < j + 1) (h : j < as.length) :
    as.extract i (j + 1) = (as.extract i j) ++ [as[j]] := by
  apply ext_getElem
  · simp
    omega
  · intro _ h₁ h₂
    simp only [length_extract, length_append, length_singleton] at h₁ h₂
    simp only [getElem_extract, getElem_append]
    split
    · rfl
    · rename_i h₃
      simp at h₃ ⊢
      congr 1
      omega

theorem extract_sub_one (h : j < as.length) :
    as.extract i (j - 1) = (as.extract i j).dropLast := by
  apply ext_getElem
  · simp; omega
  · intro _ h₁ h₂
    simp only [length_extract, length_dropLast] at h₁ h₂
    simp only [getElem_extract, getElem_dropLast]

@[grind =]
theorem extract_set {a : α} :
    (as.set k a).extract i j =
      if k < i then
        as.extract i j
      else
        (as.extract i j).set (k - i) a := by
  split
  · apply ext_getElem
    · simp
    · simp only [length_extract, length_set, getElem_extract]
      intros
      rw [getElem_set_ne (by omega)]
  · apply ext_getElem
    · simp
    · simp only [length_extract, length_set, getElem_extract]
      simp [getElem_set, Nat.sub_eq_iff_eq_add' (Nat.not_lt.mp ‹_›)]

@[grind =]
theorem set_extract {a : α} :
    (as.extract i j).set k a = (as.set (i + k) a).extract i j := by
  apply ext_getElem <;> simp [getElem_set]

theorem set_eq_extract_append_cons_extract (h : i < as.length) :
    as.set i a = as.extract 0 i ++ (a :: (as.extract (i + 1) as.length)) := by
  simp [set_eq_take_append_cons_drop, extract_eq_drop_take', h]

@[simp, grind =]
theorem extract_append :
    (as ++ bs).extract i j = as.extract i j ++ bs.extract (i - as.length) (j - as.length) := by
  apply ext_getElem
  · simp; omega
  · intro _ h₁ h₂
    simp only [length_extract, length_append] at h₁ h₂
    simp only [getElem_append, length_extract, getElem_extract]
    split
    · split
      · rfl
      · omega
    · split
      · omega
      · congr 1
        omega

theorem extract_append_left :
    (as ++ bs).extract 0 as.length = as.extract 0 as.length := by
  simp

theorem extract_append_right :
    (as ++ bs).extract as.length (as.length + i) = bs.extract 0 i := by
  simp

@[simp, grind _=_]
theorem extract_append_extract :
    as.extract i j ++ as.extract j k = as.extract (min i j) (max j k) := by
  apply ext_getElem
  · simp only [length_append, length_extract]
    omega
  · intro p h₁ h₂
    simp only [length_append, length_extract] at h₁ h₂
    simp only [getElem_append, length_extract, getElem_extract]
    split <;>
    · congr 1
      omega

@[simp, grind =]
theorem map_extract {f : α → β} :
    (as.extract i j).map f = (as.map f).extract i j := by
  apply ext_getElem <;> simp

@[simp, grind =]
theorem extract_replicate {a : α} {n : Nat} :
    (replicate n a).extract i j = replicate (min j n - i) a := by
  apply ext_getElem <;> simp

theorem extract_eq_extract_right :
    as.extract i j = as.extract i j' ↔ min (j - i) (as.length - i) = min (j' - i) (as.length - i) := by
  simp [List.extract_eq_take_drop]

theorem extract_eq_extract_left :
    as.extract i j = as.extract i' j ↔ min j as.length - i = min j as.length - i' := by
  constructor
  · intro h
    replace h := congrArg List.length h
    simpa using h
  · intro h
    apply ext_getElem
    · simpa
    · intro _ h₁ h₂
      simp only [length_extract] at h₁ h₂
      simp only [getElem_extract]
      congr 1
      omega

@[simp]
theorem extract_eq_self_iff :
    as.extract i j = as ↔ as.length = 0 ∨ i = 0 ∧ as.length ≤ j := by
  constructor
  · intro h
    replace h := congrArg List.length h
    simp at h
    omega
  · intro h
    apply ext_getElem
    · simp; omega
    · intro _ h₁ h₂
      simp only [length_extract] at h₁
      simp only [getElem_extract]
      congr 1
      omega

theorem extract_eq_self_of_le (h : as.length ≤ j) :
    as.extract 0 j = as :=
  extract_eq_self_iff.2 (.inr ⟨rfl, h⟩)

theorem le_of_extract_eq_self (h : as.extract i j = as) :
    as.length ≤ j := by
  replace h := congrArg List.length h
  simp at h
  omega

theorem extract_add_left :
    as.extract (i + j) k = (as.extract i k).extract j (k - i) := by
  simp [extract_eq_extract_right]
  omega

theorem mem_extract_iff_getElem {a : α} :
    a ∈ as.extract i j ↔ ∃ (k : Nat) (hm : k < min j as.length - i), as[i + k] = a := by
  simp [extract_eq_drop_take', mem_drop_iff_getElem]
  constructor <;>
  · rintro ⟨k, h, rfl⟩
    exact ⟨k, by omega, rfl⟩

@[grind =]
theorem extract_reverse :
    as.reverse.extract i j = (as.extract (as.length - j) (as.length - i)).reverse := by
  apply ext_getElem
  · simp
    omega
  · intro _ h₁ h₂
    simp only [length_extract, length_reverse] at h₁ h₂
    simp only [getElem_extract, getElem_reverse, length_extract]
    congr 1
    omega

@[grind =]
theorem reverse_extract :
    (as.extract i j).reverse = as.reverse.extract (as.length - j) (as.length - i) := by
  rw [extract_reverse, reverse_inj]
  simp +singlePass only [extract_eq_extract_min]
  congr 1 <;> omega

theorem extract_takeWhile {i : Nat} :
    (as.takeWhile p).extract 0 i = (as.extract 0 i).takeWhile p := by
  simp [take_takeWhile, List.extract_eq_drop_take']

theorem takeWhile_eq_extract_findIdx_not {p : α → Bool} :
    takeWhile p xs = xs.extract 0 (xs.findIdx (fun a => !p a)) := by
  simp [takeWhile_eq_take_findIdx_not, extract_eq_drop_take']

@[simp]
theorem extract_cons_of_start_pos (h : 0 < i) :
    (a :: as).extract i j = as.extract (i - 1) (j - 1) := by
  apply ext_getElem
  · simp; omega
  · intro p h₁ h₂
    have : i + p ≠ 0 := by omega
    simp only [getElem_extract, getElem_cons, reduceDIte, *]
    congr 1; omega

@[simp]
theorem extract_cons_zero_of_stop_pos (h : 0 < j) :
    (a :: as).extract 0 j = a :: as.extract 0 (j - 1) := by
  apply ext_getElem
  · simp; omega
  · intro p h₁ h₂
    simp only [getElem_extract, Nat.zero_add, getElem_cons]

theorem extract_cons :
    (a :: as).extract i j =
      if 0 < i ∨ j = 0 then as.extract (i - 1) (j - 1) else a :: as.extract (i - 1) (j - 1) := by
  split <;> rename_i h
  · cases h
    · exact extract_cons_of_start_pos ‹_›
    · simp [*]
  · simp only [not_or, Nat.not_lt, Nat.le_zero_eq, Nat.ne_zero_iff_zero_lt] at h
    simp +contextual [extract_cons_zero_of_stop_pos, *]

end List
