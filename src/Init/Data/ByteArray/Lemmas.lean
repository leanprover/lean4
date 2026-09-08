/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.ByteArray.BootstrapLemmas
import Init.ByCases
import Init.Data.Array.Bootstrap
import Init.Data.Array.Extract
import Init.Data.Array.Lemmas
import Init.Data.BitVec.Bootstrap
import Init.Data.BitVec.Lemmas
import Init.Omega

public section

namespace ByteArray

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
  simpa using! Array.set_eq_push_extract_append_extract _

theorem getElem_set {as : ByteArray} {i : Nat} (h : i < as.size) {a : UInt8} {j : Nat}
    (hj : j < (as.set i a h).size) :
    (as.set i a h)[j] = if i = j then a else as[j]'(by simpa using hj) := by
  simp [getElem_eq_getElem_data, Array.getElem_set]

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
    · rw [dite_eq_right (by omega)]
  | case2 => rw [dite_eq_left (by omega), BitVec.getElem_cast]

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
  simp [Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]

theorem getBitVecLE_add_one {bs : ByteArray} {i : Nat} {n : Nat} (h) :
    getBitVecLE bs i (n + 1) h = getBitVecLE bs (i + 1) n ++ bs[i].toBitVec := by
  rw [getBitVecLE_add]; simp

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
    · rw [ite_eq_right (by omega)]
  | case2 => rw [ite_eq_left (by omega), BitVec.getMsbD_cast]

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
  simp [Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]

theorem getBitVecBE_add_one {bs : ByteArray} {i : Nat} {n : Nat} (h) :
    getBitVecBE bs i (n + 1) h =
      (bs[i].toBitVec ++ getBitVecBE bs (i + 1) n).cast (Nat.add_comm ..) := by
  rw [getBitVecBE_add]; simp

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
    · rw [ite_eq_left (by omega)]
    split
    · simp [show j = i + k by omega]
    · rw [getElem_set, ite_eq_right (by omega)]
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
    · rw [ite_eq_left (by omega), BitVec.extractLsb'_append_eq_of_le (by omega)]; congr; omega
    split
    · rw [ite_eq_left (by omega), BitVec.extractLsb'_append_eq_of_add_le (by omega)]
    · rw [ite_eq_right (by omega)]

theorem getBitVecLE_setBitVecLE_self {bs : ByteArray} {i nbytes : Nat} {val : BitVec (8 * nbytes)}
    {hi} : (bs.setBitVecLE i nbytes val hi).getBitVecLE i nbytes (by simpa using hi) = val := by
  ext j hj
  rw [getElem_getBitVecLE, getElem_setBitVecLE, ite_eq_left (by omega)]
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
    · rw [ite_eq_left (by omega)]
    split
    · simp [show j = i + k by omega]; congr 2; omega
    · rw [getElem_set, ite_eq_right (by omega)]
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
    · rw [ite_eq_left (by omega), BitVec.extractLsb'_append_eq_of_add_le (by omega)]; congr 2; omega
    split
    · rw [ite_eq_left (by omega), BitVec.extractLsb'_append_eq_of_le (by omega)]; congr; omega
    · rw [ite_eq_right (by omega)]

theorem getBitVecBE_setBitVecBE_self {bs : ByteArray} {i nbytes : Nat} {val : BitVec (8 * nbytes)}
    {hi} : (bs.setBitVecBE i nbytes val hi).getBitVecBE i nbytes (by simpa using hi) = val := by
  ext j hj
  rw [getElem_getBitVecBE, getElem_setBitVecBE, ite_eq_left (by omega)]
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
  · simp only [Nat.not_le_of_lt ‹_›, false_and, ↓reduceIte]
  · rename_i h'
    replace h' := Nat.le_of_not_lt h'
    simp only [← Nat.sub_lt_iff_lt_add', h', true_and]
    split
    · rfl
    · congr; omega

theorem getElem!_push_lt (data : ByteArray) (b : UInt8) (i : Nat) (hi : i < data.size) :
    (data.push b)[i]! = data[i]! := by
  have hi' : i < (data.push b).size := by
    simp only [ByteArray.size_push]
    omega
  rw [getElem!_pos (data.push b) i hi', getElem!_pos data i hi]
  exact Array.getElem_push_lt hi

@[simp] theorem getElem!_push_eq (data : ByteArray) (b : UInt8) :
    (data.push b)[data.size]! = b := by
  have h : data.size < (data.push b).size := by
    simp only [ByteArray.size_push]
    omega
  rw [getElem!_pos (data.push b) data.size h]
  exact Array.getElem_push_eq

@[grind =] theorem getElem!_push (data : ByteArray) (b : UInt8) (i : Nat) :
    (data.push b)[i]! = if i = data.size then b else data[i]! := by
  split
  · subst i
    exact getElem!_push_eq data b
  · by_cases hi : i < data.size
    · exact getElem!_push_lt data b i hi
    · rw [getElem!_neg data i hi,
        getElem!_neg (data.push b) i (by simp only [ByteArray.size_push]; omega)]

private theorem getElem!_eq_data_getElem! (data : ByteArray) (i : Nat) :
    data[i]! = data.data[i]! := by
  by_cases h : i < data.size
  · rw [getElem!_pos data i h, getElem!_pos data.data i h]
    rfl
  · rw [getElem!_neg data i h, getElem!_neg data.data i h]

@[simp, grind =] theorem size_set! (data : ByteArray) (i : Nat) (v : UInt8) :
    (data.set! i v).size = data.size := by
  show (data.data.setIfInBounds i v).size = data.data.size
  exact Array.size_setIfInBounds ..

@[simp] theorem getElem!_set!_self (data : ByteArray) (i : Nat) (v : UInt8) (h : i < data.size) :
    (data.set! i v)[i]! = v := by
  rw [getElem!_eq_data_getElem!]
  show (data.data.set! i v)[i]! = v
  simp only [Array.set!_eq_setIfInBounds, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_self_of_lt h, Option.getD_some]

@[simp] theorem getElem!_set!_ne (data : ByteArray) (i j : Nat) (v : UInt8) (hij : i ≠ j) :
    (data.set! i v)[j]! = data[j]! := by
  rw [getElem!_eq_data_getElem!, getElem!_eq_data_getElem!]
  show (data.data.set! i v)[j]! = data.data[j]!
  simp only [Array.set!_eq_setIfInBounds, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_ne hij]

@[grind =] theorem getElem!_set! (data : ByteArray) (i : Nat) (v : UInt8) (j : Nat) (h : i < data.size) :
    (data.set! i v)[j]! = if i = j then v else data[j]! := by
  split
  · next hij => subst hij; exact getElem!_set!_self data i v h
  · next hij => exact getElem!_set!_ne data i j v hij

@[simp] theorem getElem_set!_ne (data : ByteArray) (i j : Nat) (v : UInt8) (hij : i ≠ j)
    (hj : j < data.size) :
    (data.set! i v)[j]'(by rw [size_set!]; exact hj) = data[j] := by
  rw [← getElem!_pos (data.set! i v) j (by rw [size_set!]; exact hj),
    ← getElem!_pos data j hj,
    getElem!_set!_ne _ _ _ _ hij]

@[simp] theorem getElem_set!_self (data : ByteArray) (i : Nat) (v : UInt8) (h : i < data.size) :
    (data.set! i v)[i]'(by rw [size_set!]; exact h) = v := by
  rw [← getElem!_pos (data.set! i v) i (by rw [size_set!]; exact h),
    getElem!_set!_self _ _ _ h]

@[grind =] theorem getElem_set! (data : ByteArray) (i j : Nat) (v : UInt8) (h : i < data.size)
    (hj : j < data.size) :
    (data.set! i v)[j]'(by rw [size_set!]; exact hj) = if i = j then v else data[j] := by
  split
  · next hij => subst hij; exact getElem_set!_self data i v h
  · next hij => exact getElem_set!_ne data i j v hij hj

end ByteArray
