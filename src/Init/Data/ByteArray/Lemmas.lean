/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.ByteArray.Basic
import Init.ByCases
import Init.Data.Array.Bootstrap
import Init.Data.Array.Extract
import Init.Data.Array.Lemmas
import Init.Data.BitVec.Bootstrap
import Init.Data.BitVec.Lemmas
import Init.Omega

public section

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
  rw [Array.getElem_append_left (by simpa)]; rfl

theorem getElem_append_right {i : Nat} {a b : ByteArray} {h : i < (a ++ b).size}
    (hle : a.size ≤ i) : (a ++ b)[i] = b[i - a.size]'(by simp_all; omega) := by
  simp only [getElem_eq_getElem_data, data_append]
  rw [Array.getElem_append_right (by simpa)]
  simp; rfl

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
  simp [getElem_eq_getElem_data]; rfl

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
    simp [ByteArray.getElem_eq_getElem_data]; rfl

theorem extract_add_two {a : ByteArray} {i : Nat} (ha : i + 2 ≤ a.size) :
    a.extract i (i + 2) = [a[i], a[i + 1]].toByteArray := by
  rw [extract_eq_extract_append_extract (i + 1) (by simp) (by omega),
    extract_add_one (by omega), extract_add_one (by omega)]
  simp [← List.toByteArray_append]; rfl

theorem extract_add_three {a : ByteArray} {i : Nat} (ha : i + 3 ≤ a.size) :
    a.extract i (i + 3) = [a[i], a[i + 1], a[i + 2]].toByteArray := by
  rw [extract_eq_extract_append_extract (i + 1) (by simp) (by omega),
    extract_add_one (by omega), extract_add_two (by omega)]
  simp [← List.toByteArray_append]; rfl

theorem extract_add_four {a : ByteArray} {i : Nat} (ha : i + 4 ≤ a.size) :
    a.extract i (i + 4) = [a[i], a[i + 1], a[i + 2], a[i + 3]].toByteArray := by
  rw [extract_eq_extract_append_extract (i + 1) (by simp) (by omega),
    extract_add_one (by omega), extract_add_three (by omega)]
  simp [← List.toByteArray_append]; rfl

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

@[simp]
theorem size_set {as : ByteArray} {i : Nat} {h : i < as.size} {a : UInt8} :
    (as.set i a h).size = as.size := by
  simp [← size_data]

theorem set_eq_push_extract_append_extract {as : ByteArray} {i : Nat} (h : i < as.size) {a : UInt8} :
    as.set i a h = (as.extract 0 i).push a ++ as.extract (i + 1) as.size := by
  ext1
  simpa using Array.set_eq_push_extract_append_extract _

theorem getElem_set {as : ByteArray} {i : Nat} (h : i < as.size) {a : UInt8} {j : Nat}
    (hj : j < (as.set i a h).size) :
    (as.set i a h)[j] = if i = j then a else as[j]'(by simpa using hj) := by
  simpa using Array.getElem_set h hj

@[simp]
theorem getElem_set_self {as : ByteArray} {i : Nat} (h : i < as.size) {a : UInt8} :
    (as.set i a h)[i]'(by simpa using h) = a := by
  simp [getElem_set]

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

@[simp]
theorem _root_.List.toByteArray_inj {l l' : List UInt8} : l.toByteArray = l'.toByteArray ↔ l = l' := by
  simp [ByteArray.ext_iff]

theorem extract_eq_extract_iff_getElem {as bs : ByteArray} {i j len : Nat}
    (hi : i + len ≤ as.size) (hj : j + len ≤ bs.size) :
    as.extract i (i + len) = bs.extract j (j + len) ↔ ∀ k, (hk : k < len) → as[i + k] = bs[j + k] := by
  induction len with
  | zero => simp
  | succ len ih =>
    rw [← Nat.add_assoc, ← Nat.add_assoc, ByteArray.extract_eq_extract_append_extract (i + len) (by omega) (by omega),
      ByteArray.extract_eq_extract_append_extract (a := bs) (j + len) (by omega) (by omega),
      ByteArray.append_eq_append_iff_of_size_eq_left (by simp; omega), ih (by omega) (by omega),
      ByteArray.extract_add_one (by omega), ByteArray.extract_add_one (by omega)]
    simp only [List.toByteArray_inj, List.cons.injEq, and_true]
    refine ⟨fun ⟨h, h'⟩ k hk => ?_, fun h => ⟨fun k hk => h k (by omega), h len (by omega)⟩⟩
    by_cases hk' : k < len
    · exact h k hk'
    · exact (by omega : k = len) ▸ h'

private theorem getBitVecLE.getElem_go {bs i n h k hk acc j hj} :
    (go bs i n h k hk acc)[j]'hj =
      if h : j < 8 * k then acc[j] else bs[i + j / 8].toBitVec[j % 8] := by
  fun_induction go with
  | case1 k _ acc hk b ih =>
    rw [ih]; split
    · simp only [BitVec.getElem_cast, BitVec.getElem_append, b]
      split
      · rfl
      · congr <;> omega
    · rw [dif_neg (by omega)]
  | case2 => rw [dif_pos (by omega), BitVec.getElem_cast]

@[grind =]
theorem getElem_getBitVecLE {bs : ByteArray} {i nbytes : Nat}
    (hi : i + nbytes ≤ bs.size) (hj : j < 8 * nbytes) :
    (getBitVecLE bs i nbytes hi)[j]'hj = bs[i + j / 8].toBitVec[j % 8] := by
  simp [getBitVecLE, getBitVecLE.getElem_go]

@[simp]
theorem getBitVecLE_zero {bs : ByteArray} {i : Nat} (h) :
    getBitVecLE bs i 0 h = 0#0 := BitVec.eq_nil _

theorem getBitVecLE_add {bs : ByteArray} {i : Nat} (m n : Nat) (h) :
    getBitVecLE bs i (n + m) h =
      (getBitVecLE bs (i + m) n ++ getBitVecLE bs i m).cast (by omega) := by
  ext i hi
  simp +contextual only [getElem_getBitVecLE, BitVec.getElem_cast, BitVec.getElem_append,
    Nat.sub_mul_div, left_eq_dite_iff, Nat.not_lt, Nat.sub_mul_mod]
  intro; congr 3; omega

@[simp]
theorem getBitVecLE_one {bs : ByteArray} {i : Nat} (h) :
    getBitVecLE bs i 1 h = bs[i].toBitVec := by
  ext j hj
  rw [ByteArray.getElem_getBitVecLE]
  simp [Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]; rfl

theorem getBitVecLE_add_one {bs : ByteArray} {i : Nat} {n : Nat} (h) :
    getBitVecLE bs i (n + 1) h = getBitVecLE bs (i + 1) n ++ bs[i].toBitVec := by
  rw [getBitVecLE_add]; simp; rfl

theorem extractLsb'_getBitVecLE_eight {bs : ByteArray} {i : Nat} {n : Nat} {h} {k : Nat}
    (hk : k < n) : (getBitVecLE bs i n h).extractLsb' (8 * k) 8 = bs[i + k].toBitVec := by
  ext j hj
  rw [BitVec.getElem_extractLsb', BitVec.getLsbD_eq_getElem (by omega), getElem_getBitVecLE]
  simp [Nat.mul_add_div, Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]

private theorem getBitVecBE.getMsbD_go {bs i n h k hk acc j} (hj : j < 8 * n) :
    (go bs i n h k hk acc).getMsbD j =
      if j < 8 * k then acc.getMsbD j else bs[i + j / 8].toBitVec.getMsbD (j % 8) := by
  fun_induction go with
  | case1 k _ acc hk b ih =>
    rw [ih]; split
    · simp only [BitVec.getMsbD_cast, BitVec.getMsbD_append, b, ← Nat.not_lt, ite_not]
      split
      · rfl
      · congr <;> omega
    · rw [if_neg (by omega)]
  | case2 => rw [if_pos (by omega), BitVec.getMsbD_cast]

theorem getMsbD_getBitVecBE {bs : ByteArray} {i nbytes : Nat}
    (hi : i + nbytes ≤ bs.size) (hj : j < 8 * nbytes) :
    (getBitVecBE bs i nbytes hi).getMsbD j = bs[i + j / 8].toBitVec.getMsbD (j % 8) := by
  simp [getBitVecBE, getBitVecBE.getMsbD_go, hj]

@[grind =]
theorem getElem_getBitVecBE {bs : ByteArray} {i nbytes : Nat}
    (hi : i + nbytes ≤ bs.size) (hj : j < 8 * nbytes) :
    (getBitVecBE bs i nbytes hi)[j] = bs[i + nbytes - j / 8 - 1].toBitVec[j % 8] := by
  rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_eq_getMsbD, getMsbD_getBitVecBE _ (by omega),
    decide_eq_true hj, Bool.true_and, BitVec.getMsbD_eq_getLsbD, decide_eq_true (by omega),
    Bool.true_and, BitVec.getLsbD_eq_getElem (by omega)]
  congr <;> omega

@[simp]
theorem getBitVecBE_zero {bs : ByteArray} {i : Nat} (h) :
    getBitVecBE bs i 0 h = 0#0 := BitVec.eq_nil _

theorem getBitVecBE_add {bs : ByteArray} {i : Nat} (m n : Nat) (h) :
    getBitVecBE bs i (n + m) h =
      (getBitVecBE bs i m ++ getBitVecBE bs (i + m) n).cast (by omega) := by
  apply BitVec.eq_of_getMsbD_eq
  intro j hj
  simp +contextual only [hj, getMsbD_getBitVecBE, BitVec.getMsbD_cast, BitVec.getMsbD_append,
    Nat.sub_lt_iff_lt_add, ← Nat.mul_add, Nat.sub_mul_div, Nat.sub_mul_mod, ← dite_eq_ite,
    not_false_eq_true, Nat.lt_of_not_le, right_eq_dite_iff]
  intro; congr 3; omega

@[simp]
theorem getBitVecBE_one {bs : ByteArray} {i : Nat} (h) :
    getBitVecBE bs i 1 h = bs[i].toBitVec := by
  apply BitVec.eq_of_getMsbD_eq
  intro j hj
  rw [ByteArray.getMsbD_getBitVecBE _ hj]
  simp [Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]; rfl

theorem getBitVecBE_add_one {bs : ByteArray} {i : Nat} {n : Nat} (h) :
    getBitVecBE bs i (n + 1) h =
      (bs[i].toBitVec ++ getBitVecBE bs (i + 1) n).cast (Nat.add_comm ..) := by
  rw [getBitVecBE_add]; simp; rfl

theorem extractLsb'_getBitVecBE_eight {bs : ByteArray} {i : Nat} {n : Nat} {h} {k : Nat}
    (hk : k < n) : (getBitVecBE bs i n h).extractLsb' (8 * k) 8 = bs[i + n - k - 1].toBitVec := by
  ext j hj
  rw [BitVec.getElem_extractLsb', BitVec.getLsbD_eq_getElem (by omega), getElem_getBitVecBE]
  simp [Nat.mul_add_div, Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]

private theorem setBitVecLE.size_go :
    (go i nbytes val k hk acc h).size = acc.size := by
  fun_induction go <;> simp_all +zetaDelta

@[simp, grind =]
theorem size_setBitVecLE {bs : ByteArray} {i nbytes : Nat} {val : BitVec (8 * nbytes)}
    {hi : i + nbytes ≤ bs.size} : (bs.setBitVecLE i nbytes val hi).size = bs.size := by
  rw [setBitVecLE, setBitVecLE.size_go]

private theorem setBitVecLE.getElem_go :
    (go i nbytes val k hk acc h)[j]'hj =
      if i + k ≤ j ∧ j < i + nbytes then UInt8.ofBitVec (val.extractLsb' (8 * (j - i)) 8)
      else acc[j]'(by simpa [size_go] using hj) := by
  fun_induction go with
  | @case1 k _ acc h hk acc' ih =>
    unfold go
    simp only [hk, ↓reduceDIte, ih, acc']
    split
    · rw [if_pos (by omega)]
    split
    · simp [show j = i + k by omega]
    · rw [getElem_set, if_neg (by omega)]
  | case2 k hk acc h hk' =>
    unfold go
    simp only [hk', ↓reduceDIte, right_eq_ite_iff, and_imp]
    intros; omega

@[grind =]
theorem getElem_setBitVecLE {bs : ByteArray} {i nbytes : Nat} {val : BitVec (8 * nbytes)} {j : Nat}
    {hi : i + nbytes ≤ bs.size} (hj : j < (bs.setBitVecLE i nbytes val hi).size) :
    (bs.setBitVecLE i nbytes val hi)[j] =
      if i ≤ j ∧ j < i + nbytes then UInt8.ofBitVec (val.extractLsb' (8 * (j - i)) 8)
      else bs[j]'(by simpa using hj) := by
  simp [setBitVecLE, setBitVecLE.getElem_go]

@[simp]
theorem setBitVecLE_zero {bs : ByteArray} {i : Nat} {val hi} :
    bs.setBitVecLE i 0 val hi = bs := by
  apply ByteArray.ext_getElem <;> simp +contextual [getElem_setBitVecLE, Nat.not_lt_of_le]

@[simp]
theorem setBitVecLE_one {bs : ByteArray} {i : Nat} {val hi} :
    bs.setBitVecLE i 1 val hi = bs.set i (.ofBitVec val) hi := by
  apply ByteArray.ext_getElem
  · simp
  · intro j hj hj'
    simp only [getElem_setBitVecLE, getElem_set]
    split
    · simp [show i = j by omega]
    · simp [show i ≠ j by omega]

@[simp]
theorem setBitVecLE_cast {bs : ByteArray} {i : Nat} {n n'} {val : BitVec (8 * n)} {hi}
    (hn : 8 * n = 8 * n') : bs.setBitVecLE i n' (val.cast hn) = bs.setBitVecLE i n val := by
  rw [Nat.mul_right_inj (by decide)] at hn
  subst hn; rfl

theorem setBitVecLE_append {bs : ByteArray} {i : Nat} {n n' k}
    {val : BitVec (8 * n)} {val' : BitVec (8 * n')} {hk} {hi} :
    bs.setBitVecLE i k ((val ++ val').cast hk) hi =
      (bs.setBitVecLE i n' val').setBitVecLE (i + n') n val (by simp; omega) := by
  apply ByteArray.ext_getElem
  · simp
  · intro j hj hj'
    simp only [getElem_setBitVecLE, ← apply_ite UInt8.ofBitVec, UInt8.ofBitVec.injEq,
      BitVec.extractLsb'_cast]
    symm; split
    · rw [if_pos (by omega), BitVec.extractLsb'_append_eq_of_le (by omega)]; congr; omega
    split
    · rw [if_pos (by omega), BitVec.extractLsb'_append_eq_of_add_le (by omega)]
    · rw [if_neg (by omega)]

theorem getBitVecLE_setBitVecLE_self {bs : ByteArray} {i nbytes : Nat} {val : BitVec (8 * nbytes)}
    {hi} : (bs.setBitVecLE i nbytes val hi).getBitVecLE i nbytes (by simpa using hi) = val := by
  ext j hj
  rw [getElem_getBitVecLE, getElem_setBitVecLE, if_pos (by omega)]
  simp [Nat.div_add_mod, hj]

private theorem setBitVecBE.size_go :
    (go i nbytes val k hk acc h).size = acc.size := by
  fun_induction go <;> simp_all +zetaDelta

@[simp, grind =]
theorem size_setBitVecBE {bs : ByteArray} {i nbytes : Nat} {val : BitVec (8 * nbytes)}
    {hi : i + nbytes ≤ bs.size} : (bs.setBitVecBE i nbytes val hi).size = bs.size := by
  rw [setBitVecBE, setBitVecBE.size_go]

private theorem setBitVecBE.getElem_go :
    (go i nbytes val k hk acc h)[j]'hj =
      if i + k ≤ j ∧ j < i + nbytes then
        UInt8.ofBitVec (val.extractLsb' (8 * (i + nbytes - j - 1)) 8)
      else acc[j]'(by simpa [size_go] using hj) := by
  fun_induction go with
  | @case1 k _ acc h hk acc' ih =>
    unfold go
    simp only [hk, ↓reduceDIte, ih, acc']
    split
    · rw [if_pos (by omega)]
    split
    · simp [show j = i + k by omega]; congr 2; omega
    · rw [getElem_set, if_neg (by omega)]
  | case2 k hk acc h hk' =>
    unfold go
    simp only [hk', ↓reduceDIte, right_eq_ite_iff, and_imp]
    intros; omega

@[grind =]
theorem getElem_setBitVecBE {bs : ByteArray} {i nbytes : Nat} {val : BitVec (8 * nbytes)} {j : Nat}
    {hi : i + nbytes ≤ bs.size} (hj : j < (bs.setBitVecBE i nbytes val hi).size) :
    (bs.setBitVecBE i nbytes val hi)[j] =
      if i ≤ j ∧ j < i + nbytes then
        UInt8.ofBitVec (val.extractLsb' (8 * (i + nbytes - j - 1)) 8)
      else bs[j]'(by simpa using hj) := by
  simp [setBitVecBE, setBitVecBE.getElem_go]

@[simp]
theorem setBitVecBE_zero {bs : ByteArray} {i : Nat} {val hi} :
    bs.setBitVecBE i 0 val hi = bs := by
  apply ByteArray.ext_getElem <;> simp +contextual [getElem_setBitVecBE, Nat.not_lt_of_le]

@[simp]
theorem setBitVecBE_one {bs : ByteArray} {i : Nat} {val hi} :
    bs.setBitVecBE i 1 val hi = bs.set i (.ofBitVec val) hi := by
  apply ByteArray.ext_getElem
  · simp
  · intro j hj hj'
    simp only [getElem_setBitVecBE, getElem_set]
    split
    · simp [show i = j by omega]
    · simp [show i ≠ j by omega]

@[simp]
theorem setBitVecBE_cast {bs : ByteArray} {i : Nat} {n n'} {val : BitVec (8 * n)} {hi}
    (hn : 8 * n = 8 * n') : bs.setBitVecBE i n' (val.cast hn) = bs.setBitVecBE i n val := by
  rw [Nat.mul_right_inj (by decide)] at hn
  subst hn; rfl

theorem setBitVecBE_append {bs : ByteArray} {i : Nat} {n n' k}
    {val : BitVec (8 * n)} {val' : BitVec (8 * n')} {hk} {hi} :
    bs.setBitVecBE i k ((val ++ val').cast hk) hi =
      (bs.setBitVecBE i n val).setBitVecBE (i + n) n' val' (by simp; omega) := by
  apply ByteArray.ext_getElem
  · simp
  · intro j hj hj'
    simp only [getElem_setBitVecBE, ← apply_ite UInt8.ofBitVec, UInt8.ofBitVec.injEq,
      BitVec.extractLsb'_cast]
    symm; split
    · rw [if_pos (by omega), BitVec.extractLsb'_append_eq_of_add_le (by omega)]; congr 2; omega
    split
    · rw [if_pos (by omega), BitVec.extractLsb'_append_eq_of_le (by omega)]; congr; omega
    · rw [if_neg (by omega)]

theorem getBitVecBE_setBitVecBE_self {bs : ByteArray} {i nbytes : Nat} {val : BitVec (8 * nbytes)}
    {hi} : (bs.setBitVecBE i nbytes val hi).getBitVecBE i nbytes (by simpa using hi) = val := by
  ext j hj
  rw [getElem_getBitVecBE, getElem_setBitVecBE, if_pos (by omega)]
  simp only [BitVec.getElem_extractLsb']
  rw [show 8 * _ + j % 8 = j by omega]
  simp [hj]

@[simp]
theorem size_fill {bs : ByteArray} {start size : Nat} {val : UInt8}
    (h : start + size ≤ bs.size) : (bs.fill start size val).size = bs.size := by
  rw [← size_data] at h
  simp [fill, copySlice, ← size_data] <;> omega

theorem getElem_fill {bs : ByteArray} {start size : Nat} {val : UInt8}
    (h : start + size ≤ bs.size) {i : Nat} (hi : i < (bs.fill start size val).size) :
    (bs.fill start size val)[i] =
      if start ≤ i ∧ i < start + size then val else bs[i]'(size_fill h ▸ hi) := by
  have hstart : start ≤ bs.data.size := Nat.le_of_add_right_le h
  have hsize : size ≤ bs.data.size := Nat.le_of_add_right_le (Nat.add_comm .. ▸ h)
  simp only [fill, copySlice, Nat.zero_add, Array.size_replicate, Nat.sub_zero, Nat.min_self,
    Nat.min_eq_left, Array.append_assoc, getElem_eq_getElem_data, Array.getElem_append, Array.size_extract,
    hstart, Array.getElem_extract, Array.getElem_replicate]
  split
  · simp only [Nat.not_le_of_lt ‹_›, false_and, ↓reduceIte]; rfl
  · rename_i h'
    replace h' := Nat.le_of_not_lt h'
    simp only [← Nat.sub_lt_iff_lt_add', h', true_and]
    split
    · rfl
    · congr; omega

protected theorem beq_iff_eq {as bs : ByteArray} : as.beq bs ↔ as = bs := by
  dsimp [ByteArray.beq]
  split
  · rename_i h
    simp [sliceEq', h, Array.extract_eq_self_of_le, ← ByteArray.ext_iff]
  · rename_i h
    simp [ne_of_apply_ne size h]

instance : DecidableEq ByteArray := fun _ _ =>
  decidable_of_decidable_of_iff ByteArray.beq_iff_eq

end ByteArray
