/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.ByteArray.Basic

public section

set_option debug.byAsSorry true  -- TODO: remove after bootstrap

namespace ByteArray

-- At present the preferred normal form for empty byte arrays is `ByteArray.empty`
@[simp]
theorem emptyc_eq_empty : (∅ : ByteArray) = ByteArray.empty := rfl

@[simp]
theorem emptyWithCapacity_eq_empty : ByteArray.emptyWithCapacity 0 = ByteArray.empty := rfl

@[simp]
theorem data_empty : ByteArray.empty.data = #[] := rfl

@[simp]
theorem data_extract {a : ByteArray} {b e : Nat} :
    (a.extract b e).data = a.data.extract b e := by
  simp [extract, copySlice]
  by_cases b ≤ e
  · rw [(by omega : b + (e - b) = e)]
  · rw [Array.extract_eq_empty_of_le (by omega), Array.extract_eq_empty_of_le (by omega)]

@[simp]
theorem extract_zero_size {b : ByteArray} : b.extract 0 b.size = b := by
  ext1
  simp

@[simp]
theorem extract_same {b : ByteArray} {i : Nat} : b.extract i i = ByteArray.empty := by
  ext1
  simp [Nat.min_le_left]

theorem fastAppend_eq_copySlice {a b : ByteArray} :
  a.fastAppend b = b.copySlice 0 a a.size b.size false := rfl

@[simp]
theorem _root_.List.toByteArray_append {l l' : List UInt8} :
    (l ++ l').toByteArray = l.toByteArray ++ l'.toByteArray := by
  simp [List.toByteArray_append']

@[simp]
theorem toList_data_append {l l' : ByteArray} :
    (l ++ l').data.toList = l.data.toList ++ l'.data.toList := by
  simp [← append_eq]

@[simp]
theorem data_append {l l' : ByteArray} :
    (l ++ l').data = l.data ++ l'.data := by
  simp [← Array.toList_inj]

@[simp]
theorem size_empty : ByteArray.empty.size = 0 := by
  simp [← ByteArray.size_data]

@[simp]
theorem _root_.List.data_toByteArray {l : List UInt8} :
    l.toByteArray.data = l.toArray := by
  rw [List.toByteArray]
  suffices ∀ a b, (List.toByteArray.loop a b).data = b.data ++ a.toArray by
    simpa using this l ByteArray.empty
  intro a b
  fun_induction List.toByteArray.loop a b with simp_all

@[simp]
theorem _root_.List.size_toByteArray {l : List UInt8} :
    l.toByteArray.size = l.length := by
  simp [← ByteArray.size_data]

@[simp]
theorem _root_.List.toByteArray_nil : List.toByteArray [] = ByteArray.empty := rfl

@[simp]
theorem empty_append {b : ByteArray} : ByteArray.empty ++ b = b := by
  ext1
  simp

@[simp]
theorem append_empty {b : ByteArray} : b ++ ByteArray.empty = b := by
  ext1
  simp

@[simp, grind =]
theorem size_append {a b : ByteArray} : (a ++ b).size = a.size + b.size := by
  simp [← size_data]

@[simp]
theorem size_eq_zero_iff {a : ByteArray} : a.size = 0 ↔ a = ByteArray.empty := by
  refine ⟨fun h => ?_, fun h => h ▸ ByteArray.size_empty⟩
  ext1
  simp [← Array.size_eq_zero_iff, h]

theorem getElem_eq_getElem_data {a : ByteArray} {i : Nat} {h : i < a.size} :
    a[i] = a.data[i]'(by simpa [← size_data]) := rfl

@[simp]
theorem getElem_append_left {i : Nat} {a b : ByteArray} {h : i < (a ++ b).size}
    (hlt : i < a.size) : (a ++ b)[i] = a[i] := by
  simp only [getElem_eq_getElem_data, data_append]
  rw [Array.getElem_append_left (by simpa)]

theorem getElem_append_right {i : Nat} {a b : ByteArray} {h : i < (a ++ b).size}
    (hle : a.size ≤ i) : (a ++ b)[i] = b[i - a.size]'(by simp_all; omega) := by
  simp only [getElem_eq_getElem_data, data_append]
  rw [Array.getElem_append_right (by simpa)]
  simp

@[simp]
theorem _root_.List.getElem_toByteArray {l : List UInt8} {i : Nat} {h : i < l.toByteArray.size} :
    l.toByteArray[i]'h = l[i]'(by simp_all) := by
  simp [ByteArray.getElem_eq_getElem_data]

theorem _root_.List.getElem_eq_getElem_toByteArray {l : List UInt8} {i : Nat} {h : i < l.length} :
    l[i]'h = l.toByteArray[i]'(by simp_all) := by
  simp

@[simp]
theorem size_extract {a : ByteArray} {b e : Nat} :
    (a.extract b e).size = min e a.size - b := by
  simp [← size_data]

@[simp]
theorem extract_eq_empty_iff {b : ByteArray} {i j : Nat} : b.extract i j = ByteArray.empty ↔ min j b.size ≤ i := by
  rw [← size_eq_zero_iff, size_extract]
  omega

@[simp]
theorem extract_add_left {b : ByteArray} {i j : Nat} : b.extract (i + j) i = ByteArray.empty := by
  simp only [extract_eq_empty_iff]
  exact Nat.le_trans (Nat.min_le_left _ _) (by simp)

@[simp]
theorem append_eq_empty_iff {a b : ByteArray} :
    a ++ b = ByteArray.empty ↔ a = ByteArray.empty ∧ b = ByteArray.empty := by
  simp [← size_eq_zero_iff, size_append]

@[simp]
theorem toByteArray_eq_empty {l : List UInt8} :
    l.toByteArray = ByteArray.empty ↔ l = [] := by
  simp [← ByteArray.size_eq_zero_iff]

@[simp]
theorem append_right_inj {ys₁ ys₂ : ByteArray} (xs : ByteArray) :
    xs ++ ys₁ = xs ++ ys₂ ↔ ys₁ = ys₂ := by
  simp [ByteArray.ext_iff, Array.append_right_inj]

@[simp]
theorem append_left_inj {xs₁ xs₂ : ByteArray} (ys : ByteArray) :
    xs₁ ++ ys = xs₂ ++ ys ↔ xs₁ = xs₂ := by
  simp [ByteArray.ext_iff, Array.append_left_inj]

@[simp]
theorem extract_append_extract {a : ByteArray} {i j k : Nat} :
    a.extract i j ++ a.extract j k = a.extract (min i j) (max j k) := by
  ext1
  simp

theorem extract_eq_extract_append_extract {a : ByteArray} {i k : Nat} (j : Nat)
    (hi : i ≤ j) (hk : j ≤ k) :
    a.extract i k = a.extract i j ++ a.extract j k := by
  simp
  rw [Nat.min_eq_left hi, Nat.max_eq_right hk]

theorem append_inj_left {xs₁ xs₂ ys₁ ys₂ : ByteArray} (h : xs₁ ++ ys₁ = xs₂ ++ ys₂) (hl : xs₁.size = xs₂.size) : xs₁ = xs₂ := by
  simp only [ByteArray.ext_iff, ← ByteArray.size_data, ByteArray.data_append] at *
  exact Array.append_inj_left h hl

theorem extract_append_eq_right {a b : ByteArray} {i j : Nat} (hi : i = a.size) (hj : j = a.size + b.size) :
    (a ++ b).extract i j = b := by
  subst hi hj
  ext1
  simp [← size_data]

theorem extract_append_eq_left {a b : ByteArray} {i : Nat} (hi : i = a.size) :
    (a ++ b).extract 0 i = a := by
  subst hi
  ext1
  simp

theorem extract_append_size_left {a b : ByteArray} {i : Nat} :
    (a ++ b).extract i a.size = a.extract i a.size := by
  ext1
  simp

theorem extract_append_size_add {a b : ByteArray} {i j : Nat} :
    (a ++ b).extract (a.size + i) (a.size + j) = b.extract i j := by
  ext1
  simp

theorem extract_append  {as bs : ByteArray} {i j : Nat} :
    (as ++ bs).extract i j = as.extract i j ++ bs.extract (i - as.size) (j - as.size) := by
  ext1
  simp

theorem extract_append_size_add' {a b : ByteArray} {i j k : Nat} (h : k = a.size) :
    (a ++ b).extract (k + i) (k + j) = b.extract i j := by
  cases h
  rw [extract_append_size_add]

theorem extract_extract {a : ByteArray} {i j k l : Nat} :
    (a.extract i j).extract k l = a.extract (i + k) (min (i + l) j) := by
  ext1
  simp

theorem getElem_extract_aux {xs : ByteArray} {start stop : Nat} (h : i < (xs.extract start stop).size) :
    start + i < xs.size := by
  rw [size_extract] at h; apply Nat.add_lt_of_lt_sub'; apply Nat.lt_of_lt_of_le h
  apply Nat.sub_le_sub_right; apply Nat.min_le_right

theorem getElem_extract {i : Nat} {b : ByteArray} {start stop : Nat}
    (h) : (b.extract start stop)[i]'h = b[start + i]'(getElem_extract_aux h) := by
  simp [getElem_eq_getElem_data]

theorem extract_eq_extract_left {a : ByteArray} {i i' j : Nat} :
    a.extract i j = a.extract i' j ↔ min j a.size - i = min j a.size - i' := by
  simp [ByteArray.ext_iff, Array.extract_eq_extract_left]

theorem extract_add_one {a : ByteArray} {i : Nat} (ha : i + 1 ≤ a.size) :
    a.extract i (i + 1) = [a[i]].toByteArray := by
  ext
  · simp
    omega
  · rename_i j hj hj'
    obtain rfl : j = 0 := by simpa using hj'
    simp [ByteArray.getElem_eq_getElem_data]

theorem extract_add_two {a : ByteArray} {i : Nat} (ha : i + 2 ≤ a.size) :
    a.extract i (i + 2) = [a[i], a[i + 1]].toByteArray := by
  rw [extract_eq_extract_append_extract (i + 1) (by simp) (by omega),
    extract_add_one (by omega), extract_add_one (by omega)]
  simp [← List.toByteArray_append]

theorem extract_add_three {a : ByteArray} {i : Nat} (ha : i + 3 ≤ a.size) :
    a.extract i (i + 3) = [a[i], a[i + 1], a[i + 2]].toByteArray := by
  rw [extract_eq_extract_append_extract (i + 1) (by simp) (by omega),
    extract_add_one (by omega), extract_add_two (by omega)]
  simp [← List.toByteArray_append]

theorem extract_add_four {a : ByteArray} {i : Nat} (ha : i + 4 ≤ a.size) :
    a.extract i (i + 4) = [a[i], a[i + 1], a[i + 2], a[i + 3]].toByteArray := by
  rw [extract_eq_extract_append_extract (i + 1) (by simp) (by omega),
    extract_add_one (by omega), extract_add_three (by omega)]
  simp [← List.toByteArray_append]

theorem append_assoc {a b c : ByteArray} : a ++ b ++ c = a ++ (b ++ c) := by
  ext1
  simp

@[simp]
theorem toList_empty : ByteArray.empty.toList = [] := by
  simp [ByteArray.toList, ByteArray.toList.loop]

theorem copySlice_eq_append {src : ByteArray} {srcOff : Nat} {dest : ByteArray} {destOff len : Nat} {exact : Bool} :
    ByteArray.copySlice src srcOff dest destOff len exact =
      dest.extract 0 destOff ++ src.extract srcOff (srcOff +len) ++ dest.extract (destOff + min len (src.data.size - srcOff)) dest.data.size := by
  ext1
  simp [copySlice]

@[simp]
theorem data_set {as : ByteArray} {i : Nat} {h : i < as.size} {a : UInt8} :
    (as.set i a h).data = as.data.set i a (by simpa) := by
  simp [set]

theorem set_eq_push_extract_append_extract {as : ByteArray} {i : Nat} (h : i < as.size) {a : UInt8} :
    as.set i a h = (as.extract 0 i).push a ++ as.extract (i + 1) as.size := by
  ext1
  simpa using Array.set_eq_push_extract_append_extract _

@[simp]
theorem append_toByteArray_singleton {as : ByteArray} {a : UInt8} :
    as ++ [a].toByteArray = as.push a := by
  ext1
  simp

@[simp]
theorem extract_zero_max_size {a : ByteArray} {i : Nat} : a.extract 0 (max i a.size) = a := by
  ext1
  simp [Nat.le_max_right]

theorem append_eq_append_iff_of_size_eq_left {ws xs ys zs : ByteArray} (h : ws.size = xs.size) :
    ws ++ ys = xs ++ zs ↔ ws = xs ∧ ys = zs := by
  simpa [ByteArray.ext_iff] using Array.append_eq_append_iff_of_size_eq_left h

theorem append_eq_append_iff_of_size_eq_right {ws xs ys zs : ByteArray} (h : ys.size = zs.size) :
    ws ++ ys = xs ++ zs ↔ ws = xs ∧ ys = zs := by
  simpa [ByteArray.ext_iff] using Array.append_eq_append_iff_of_size_eq_right h

@[simp]
theorem size_push {bs : ByteArray} {b : UInt8} : (bs.push b).size = bs.size + 1 := by
  rw [ByteArray.size, data_push, Array.size_push, ← ByteArray.size]

theorem ext_getElem {a b : ByteArray} (h₀ : a.size = b.size) (h : ∀ (i : Nat) hi hi', a[i]'hi = b[i]'hi') : a = b := by
  rw [ByteArray.ext_iff]
  apply Array.ext (by simpa using h₀)
  simpa [← ByteArray.getElem_eq_getElem_data]

end ByteArray
