/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robin Arnez
-/
module

prelude
import Init.Data.ByteArray.Basic
import Init.Data.Array.Lemmas
import Init.Data.UInt.Lemmas
import Init.Data.Nat.Internal

set_option linter.missingDocs true

namespace ByteArray

private theorem helperLemma {x : USize} {y z : Nat} {a b : Nat}
    (h : x.toNat + y ≤ z := by assumption) (h' : a + b ≤ y := by decide) :
    (x + USize.ofNat a).toNat + b ≤ z := by
  simp only [USize.toNat_add, USize.toNat_ofNat', Nat.add_mod_mod]
  refine Nat.le_trans ?_ h
  refine Nat.le_trans (Nat.add_le_add_right (Nat.mod_le ..) _) ?_
  rw [Nat.add_assoc]
  exact Nat.add_le_add_left h' _

/--
Interprets the value in the byte array `bs` starting at index `i`
as a 16 bit little-endian unsigned integer.
-/
def ugetUInt16LE (bs : ByteArray) (i : USize)
    (h : i.toNat + 2 ≤ bs.size := by get_elem_tactic) : UInt16 :=
  let lo := bs.uget i (Nat.lt_of_add_right_lt h)
  let hi := bs.uget (i + 1) (helperLemma (b := 1))
  lo.toUInt16 ||| (hi.toUInt16 <<< 8)

set_option linter.unusedVariables.funArgs false in
@[inline]
private unsafe def getUInt16LEImpl (bs : ByteArray) (i : Nat)
    (h : i + 2 ≤ bs.size) : UInt16 :=
  ugetUInt16LE bs (Nat.Internal.unbox i lcProof) lcProof

/--
Interprets the value in the byte array `bs` starting at index `i`
as a 16 bit little-endian unsigned integer.
-/
--@[implemented_by getUInt16LEImpl]
def getUInt16LE (bs : ByteArray) (i : Nat) (h : i + 2 ≤ bs.size := by get_elem_tactic) : UInt16 :=
  let lo := bs[i]
  let hi := bs[i + 1]
  lo.toUInt16 ||| (hi.toUInt16 <<< 8)

/--
Interprets the value in the byte array `bs` starting at index `i`
as a 16 bit big-endian unsigned integer.
-/
def ugetUInt16BE (bs : ByteArray) (i : USize)
    (h : i.toNat + 2 ≤ bs.size := by get_elem_tactic) : UInt16 :=
  let hi := bs.uget i (Nat.lt_of_add_right_lt h)
  let lo := bs.uget (i + 1) (helperLemma (b := 1))
  lo.toUInt16 ||| (hi.toUInt16 <<< 8)

/--
Interprets the value in the byte array `bs` starting at index `i`
as a 32 bit little-endian unsigned integer.
-/
def ugetUInt32LE (bs : ByteArray) (i : USize)
    (h : i.toNat + 4 ≤ bs.size := by get_elem_tactic) : UInt32 :=
  --let b1 := bs.uget i (Nat.lt_of_add_right_lt h)
  --let b2 := bs.uget (i + 1) helperLemma
  --let b3 := bs.uget (i + 2) helperLemma
  --let b4 := bs.uget (i + 3) helperLemma
  --b1.toUInt32 ||| (b2.toUInt32 <<< 8) ||| (b3.toUInt32 <<< 16) ||| (b4.toUInt32 <<< 24)
  let lo := bs.ugetUInt16LE i (Nat.le_of_add_right_le (k := 2) h)
  let hi := bs.ugetUInt16LE (i + 2) helperLemma
  lo.toUInt32 ||| (hi.toUInt32 <<< 16)

/--
Interprets the value in the byte array `bs` starting at index `i`
as a 32 bit big-endian unsigned integer.
-/
def ugetUInt32BE (bs : ByteArray) (i : USize)
    (h : i.toNat + 4 ≤ bs.size := by get_elem_tactic) : UInt32 :=
  --let b4 := bs.uget i (Nat.lt_of_add_right_lt h)
  --let b3 := bs.uget (i + 1) helperLemma
  --let b2 := bs.uget (i + 2) helperLemma
  --let b1 := bs.uget (i + 3) helperLemma
  --b1.toUInt32 ||| (b2.toUInt32 <<< 8) ||| (b3.toUInt32 <<< 16) ||| (b4.toUInt32 <<< 24)
  let hi := bs.ugetUInt16BE i (Nat.le_of_add_right_le (k := 2) h)
  let lo := bs.ugetUInt16BE (i + 2) helperLemma
  lo.toUInt32 ||| (hi.toUInt32 <<< 16)

/--
Interprets the value in the byte array `bs` starting at index `i`
as a 64 bit little-endian unsigned integer.
-/
def ugetUInt64LE (bs : ByteArray) (i : USize)
    (h : i.toNat + 8 ≤ bs.size := by get_elem_tactic) : UInt64 :=
  --let b1 := bs.uget i (Nat.lt_of_add_right_lt h)
  --let b2 := bs.uget (i + 1) helperLemma
  --let b3 := bs.uget (i + 2) helperLemma
  --let b4 := bs.uget (i + 3) helperLemma
  --let b5 := bs.uget (i + 4) helperLemma
  --let b6 := bs.uget (i + 5) helperLemma
  --let b7 := bs.uget (i + 6) helperLemma
  --let b8 := bs.uget (i + 7) helperLemma
  --b1.toUInt64 ||| (b2.toUInt64 <<< 8) ||| (b3.toUInt64 <<< 16) ||| (b4.toUInt64 <<< 24) |||
  --  (b5.toUInt64 <<< 32) ||| (b2.toUInt64 <<< 40) ||| (b3.toUInt64 <<< 48) ||| (b4.toUInt64 <<< 56)
  let lo := bs.ugetUInt32LE i (Nat.le_of_add_right_le (k := 4) h)
  let hi := bs.ugetUInt32LE (i + 4) helperLemma
  lo.toUInt64 ||| (hi.toUInt64 <<< 32)

/--
Interprets the value in the byte array `bs` starting at index `i`
as a 64 bit big-endian unsigned integer.
-/
def ugetUInt64BE (bs : ByteArray) (i : USize)
    (h : i.toNat + 8 ≤ bs.size := by get_elem_tactic) : UInt64 :=
  --let b8 := bs.uget i (Nat.lt_of_add_right_lt h)
  --let b7 := bs.uget (i + 1) helperLemma
  --let b6 := bs.uget (i + 2) helperLemma
  --let b5 := bs.uget (i + 3) helperLemma
  --let b4 := bs.uget (i + 4) helperLemma
  --let b3 := bs.uget (i + 5) helperLemma
  --let b2 := bs.uget (i + 6) helperLemma
  --let b1 := bs.uget (i + 7) helperLemma
  --b1.toUInt64 ||| (b2.toUInt64 <<< 8) ||| (b3.toUInt64 <<< 16) ||| (b4.toUInt64 <<< 24) |||
  --  (b5.toUInt64 <<< 32) ||| (b2.toUInt64 <<< 40) ||| (b3.toUInt64 <<< 48) ||| (b4.toUInt64 <<< 56)
  let hi := bs.ugetUInt32BE i (Nat.le_of_add_right_le (k := 4) h)
  let lo := bs.ugetUInt32BE (i + 4) helperLemma
  lo.toUInt64 ||| (hi.toUInt64 <<< 32)

@[simp]
theorem size_uset {bs : ByteArray} {i : USize} {val : UInt8} (h : i.toNat < bs.size) :
    (bs.uset i val).size = bs.size := by
  simp only [size, uset, Array.uset, Array.size_set]

local macro "set_tac" : tactic => `(tactic|
  ((try simp +zetaDelta only [size_uset]); first | exact helperLemma | exact helperLemma (b := 1)))

/-- Writes the value into the byte array starting at index `i` in little-endian byte order. -/
def usetUInt16LE (bs : ByteArray) (i : USize) (val : UInt16)
    (h : i.toNat + 2 ≤ bs.size := by get_elem_tactic) : ByteArray :=
  let bs := uset bs i val.toUInt8 (Nat.lt_of_add_right_lt h)
  let bs := uset bs (i + 1) (val >>> 8).toUInt8 (by simpa [bs] using helperLemma (b := 1))
  bs

@[simp]
theorem size_usetUInt16LE {bs : ByteArray} {i : USize} {val : UInt16}
    (h : i.toNat + 2 ≤ bs.size) : (bs.usetUInt16LE i val).size = bs.size := by
  simp [usetUInt16LE]

/-- Writes the value into the byte array starting at index `i` in big-endian byte order. -/
def usetUInt16BE (bs : ByteArray) (i : USize) (val : UInt16)
    (h : i.toNat + 2 ≤ bs.size := by get_elem_tactic) : ByteArray :=
  let bs := uset bs i (val >>> 8).toUInt8 (Nat.lt_of_add_right_lt h)
  let bs := uset bs (i + 1) val.toUInt8 (by simpa [bs] using helperLemma (b := 1))
  bs

@[simp]
theorem size_usetUInt16BE {bs : ByteArray} {i : USize} {val : UInt16}
    (h : i.toNat + 2 ≤ bs.size) : (bs.usetUInt16BE i val).size = bs.size := by
  simp [usetUInt16BE]

/-- Writes the value into the byte array starting at index `i` in little-endian byte order. -/
def usetUInt32LE (bs : ByteArray) (i : USize) (val : UInt32)
    (h : i.toNat + 4 ≤ bs.size := by get_elem_tactic) : ByteArray :=
  /-let bs := uset bs i val.toUInt8 (Nat.lt_of_add_right_lt h)
  let bs := uset bs (i + 1) (val >>> 8).toUInt8 (by set_tac)
  let bs := uset bs (i + 2) (val >>> 16).toUInt8 (by set_tac)
  let bs := uset bs (i + 3) (val >>> 24).toUInt8 (by set_tac)-/
  let bs := usetUInt16LE bs i val.toUInt16 (Nat.le_of_add_right_le (k := 2) h)
  let bs := usetUInt16LE bs (i + 2) (val >>> 16).toUInt16 (by simpa [bs] using helperLemma)
  bs

@[simp]
theorem size_usetUInt32LE {bs : ByteArray} {i : USize} {val : UInt32}
    (h : i.toNat + 4 ≤ bs.size) : (bs.usetUInt32LE i val).size = bs.size := by
  simp [usetUInt32LE]

/-- Writes the value into the byte array starting at index `i` in big-endian byte order. -/
def usetUInt32BE (bs : ByteArray) (i : USize) (val : UInt32)
    (h : i.toNat + 4 ≤ bs.size := by get_elem_tactic) : ByteArray :=
  /-let bs := uset bs i (val >>> 24).toUInt8 (by set_tac)
  let bs := uset bs (i + 1) (val >>> 16).toUInt8 (by set_tac)
  let bs := uset bs (i + 2) (val >>> 8).toUInt8 (by set_tac)
  let bs := uset bs (i + 3) val.toUInt8 (by set_tac)-/
  let bs := usetUInt16BE bs i (val >>> 16).toUInt16 (Nat.le_of_add_right_le (k := 2) h)
  let bs := usetUInt16BE bs (i + 2) val.toUInt16 (by simpa [bs] using helperLemma)
  bs

@[simp]
theorem size_usetUInt32BE {bs : ByteArray} {i : USize} {val : UInt32}
    (h : i.toNat + 4 ≤ bs.size) : (bs.usetUInt32BE i val).size = bs.size := by
  simp [usetUInt32BE]

/-- Writes the value into the byte array starting at index `i` in little-endian byte order. -/
def usetUInt64LE (bs : ByteArray) (i : USize) (val : UInt64)
    (h : i.toNat + 8 ≤ bs.size := by get_elem_tactic) : ByteArray :=
  /-let bs := uset bs i val.toUInt8 (by set_tac)
  let bs := uset bs (i + 1) (val >>> 8).toUInt8 (by set_tac)
  let bs := uset bs (i + 2) (val >>> 16).toUInt8 (by set_tac)
  let bs := uset bs (i + 3) (val >>> 24).toUInt8 (by set_tac)
  let bs := uset bs (i + 4) (val >>> 32).toUInt8 (by set_tac)
  let bs := uset bs (i + 5) (val >>> 40).toUInt8 (by set_tac)
  let bs := uset bs (i + 6) (val >>> 48).toUInt8 (by set_tac)
  let bs := uset bs (i + 7) (val >>> 56).toUInt8 (by set_tac)-/
  let bs := usetUInt32LE bs i val.toUInt32 (Nat.le_of_add_right_le (k := 4) h)
  let bs := usetUInt32LE bs (i + 4) (val >>> 32).toUInt32 (by simpa [bs] using helperLemma)
  bs

@[simp]
theorem size_usetUInt64LE {bs : ByteArray} {i : USize} {val : UInt64}
    (h : i.toNat + 8 ≤ bs.size) : (bs.usetUInt64LE i val).size = bs.size := by
  simp [usetUInt64LE]

/-- Writes the value into the byte array starting at index `i` in big-endian byte order. -/
def usetUInt64BE (bs : ByteArray) (i : USize) (val : UInt64)
    (h : i.toNat + 8 ≤ bs.size := by get_elem_tactic) : ByteArray :=
  /-let bs := uset bs (i + 7) val.toUInt8 (by set_tac)
  let bs := uset bs (i + 6) (val >>> 8).toUInt8 (by set_tac)
  let bs := uset bs (i + 5) (val >>> 16).toUInt8 (by set_tac)
  let bs := uset bs (i + 4) (val >>> 24).toUInt8 (by set_tac)
  let bs := uset bs (i + 3) (val >>> 32).toUInt8 (by set_tac)
  let bs := uset bs (i + 2) (val >>> 40).toUInt8 (by set_tac)
  let bs := uset bs (i + 1) (val >>> 48).toUInt8 (by set_tac)
  let bs := uset bs i (val >>> 56).toUInt8 (by set_tac)-/
  let bs := usetUInt32BE bs i (val >>> 32).toUInt32 (Nat.le_of_add_right_le (k := 4) h)
  let bs := usetUInt32BE bs (i + 4) val.toUInt32 (by simpa [bs] using helperLemma)
  bs

@[simp]
theorem size_usetUInt64BE {bs : ByteArray} {i : USize} {val : UInt64}
    (h : i.toNat + 8 ≤ bs.size) : (bs.usetUInt64BE i val).size = bs.size := by
  simp [usetUInt64BE]

theorem size_def (bs : ByteArray) : bs.size = bs.data.size := rfl

@[simp]
theorem data_extract (bs : ByteArray) (b e : Nat) :
    (bs.extract b e).data = bs.data.extract b e := by
  simp only [extract, copySlice, empty, emptyWithCapacity, Array.extract_zero, Array.empty_append,
    Nat.zero_add, Array.extract_empty, Array.append_empty]
  by_cases h : b ≤ e
  · rw [Nat.add_sub_cancel' h]
  · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_le h), Nat.add_zero]
    simp only [Nat.le_refl, Array.extract_empty_of_stop_le_start, Nat.le_of_not_le h]

@[simp]
theorem size_extract (bs : ByteArray) (b e : Nat) :
    (bs.extract b e).size = min e bs.size - b := by
  simp [size_def]

@[simp]
theorem data_append (as bs : ByteArray) :
    (as ++ bs).data = as.data ++ bs.data := by
  change (as.append bs).data = _
  simp only [ByteArray.append, copySlice, size_def, Array.extract_size, Nat.zero_add, Nat.sub_zero,
    Nat.min_self, Nat.le_add_right, Array.extract_empty_of_size_le_start, Array.append_assoc,
    Array.append_right_inj, Array.append_right_eq_self]

@[simp]
theorem size_append (as bs : ByteArray) : (as ++ bs).size = as.size + bs.size := by
  simp [size_def]

@[simp]
theorem size_mk (xs : Array UInt8) : size (mk xs) = xs.size := rfl

theorem getElem_def {xs : ByteArray} {i : Nat} (h : i < xs.size) : xs[i] = xs.data[i] := rfl

/--
Low-level function for growing or shrinking a byte array.

Note: the contents of the bytes at the end are undefined when growing which is why
this function returns a `Squash`.

If `exact` is `false`, the capacity will be doubled when grown.
-/
@[extern "lean_byte_array_set_size"]
def setSize' (bs : ByteArray) (size : @& Nat) (exact : Bool := false) :
    Squash { b : ByteArray // b.size = size ∧ ∀ (i : Nat) h h', b[i]'h = bs[i] } := by
  let b := bs.extract 0 size ++ mk (Array.replicate (size - bs.size) 0)
  refine Squash.mk ⟨b, ?_⟩
  have hsize : b.size = size := by simp [b] <;> omega
  constructor
  · exact hsize
  · intro i h h'
    rw [hsize] at h
    rw [size_def] at h'
    simp [b, getElem_def, h, h', Nat.lt_min]

/--
Replaces the bytes in the range `[start, start + size)` within `bs` with `val`.
-/
@[extern "lean_byte_array_fill"]
def fill' (bs : ByteArray) (start size : @& Nat) (val : UInt8)
    (h : start + size ≤ bs.size := by get_elem_tactic) : ByteArray :=
  (mk (Array.replicate size val)).copySlice 0 bs start size

@[simp]
theorem size_fill' {bs : ByteArray} {start size : Nat} {val : UInt8}
    (h : start + size ≤ bs.size) : (bs.fill' start size val).size = bs.size := by
  rw [size_def] at h
  simp [fill', copySlice, size_def] <;> omega

theorem getElem_fill' {bs : ByteArray} {start size : Nat} {val : UInt8}
    (h : start + size ≤ bs.size) {i : Nat} (hi : i < (bs.fill' start size val).size) :
    (bs.fill' start size val)[i] =
      if start ≤ i ∧ i < start + size then val else bs[i]'(size_fill' h ▸ hi) := by
  have hstart : start ≤ bs.data.size := Nat.le_of_add_right_le h
  have hsize : size ≤ bs.data.size := Nat.le_of_add_right_le (Nat.add_comm .. ▸ h)
  simp only [fill', copySlice, Nat.zero_add, Array.size_replicate, Nat.sub_zero, Nat.min_self,
    Nat.min_eq_left, Array.append_assoc, getElem_def, Array.getElem_append, Array.size_extract,
    hstart, Array.getElem_extract, Array.getElem_replicate]
  split
  · simp only [Nat.not_le_of_lt ‹_›, false_and, ↓reduceIte]
  · rename_i h'
    replace h' := Nat.le_of_not_lt h'
    simp only [← Nat.sub_lt_iff_lt_add', h', true_and]
    split
    · rfl
    · congr; omega

@[ext]
theorem ext {as bs : ByteArray} (h : as.size = bs.size)
    (h' : ∀ (i : Nat) h h', as[i]'h = bs[i]) : as = bs := by
  rcases as with ⟨xs⟩
  rcases bs with ⟨ys⟩
  congr
  exact Array.ext h h'

/--
Grows or shrinks a byte array. When growing, additional bytes are filled with zeroes.
-/
def setSize (bs : ByteArray) (size : Nat) (exact : Bool := false) : ByteArray :=
  Quot.liftOn (setSize' bs size exact)
    (fun bs' => if h : bs.size < size then bs'.1.fill' bs.size (size - bs.size) 0 else bs'.1)
    (fun a b _ => by
      dsimp
      split
      · ext
        · simp [a.2, b.2]
        · simp only [getElem_fill']
          split
          · rfl
          · rename_i hsize i h h' h''
            simp only [size_fill', a.2.1] at h
            simp only [Nat.le_of_lt hsize, Nat.add_sub_cancel', h, and_true, Nat.not_le] at h''
            rw [a.2.2 i _ h'', b.2.2 i _ h'']
      · ext
        · simp [a.2, b.2]
        · rename_i hbs i h h'
          replace hbs := Nat.le_of_not_lt hbs
          rw [a.2.1] at h
          rw [a.2.2 i _ (Nat.lt_of_lt_of_le h hbs),
            b.2.2 i _ (Nat.lt_of_lt_of_le h hbs)])

@[simp]
theorem size_setSize (bs : ByteArray) (size : Nat) (exact : Bool) :
    (bs.setSize size exact).size = size := by
  rw [setSize]
  rcases bs.setSize' size exact with ⟨bs⟩
  dsimp [Quot.liftOn]
  split <;> simp [bs.2]

theorem getElem_setSize {bs : ByteArray} {size : Nat} {exact : Bool} {i : Nat}
    (h : i < (bs.setSize size exact).size) :
    (bs.setSize size exact)[i] = if h : i < bs.size then bs[i] else 0 := by
  rw [size_setSize] at h
  simp only [setSize]
  have ⟨q, hq⟩ : { a // bs.setSize' size exact = a } := ⟨_, rfl⟩
  rcases q with ⟨a⟩
  simp only [Quot.liftOn, hq]
  split
  · simp only [getElem_fill']
    split
    · rename_i h
      rw [dif_neg (Nat.not_lt_of_le h.1)]
    · rename_i h h' h''
      simp only [Nat.le_of_lt h', Nat.add_sub_cancel', h, and_true, Nat.not_le] at h''
      rw [a.2.2 i _ h'', dif_pos h'']
  · rename_i h h'
    replace h' := Nat.lt_of_lt_of_le h (Nat.le_of_not_lt h')
    rw [a.2.2 i _ h', dif_pos h']

theorem getElem_setSize_eq_getElem {bs : ByteArray} {size : Nat} {exact : Bool} {i : Nat}
    {h : i < (bs.setSize size exact).size} (h' : i < bs.size) :
    (bs.setSize size exact)[i] = bs[i] := by
  simp only [getElem_setSize, h', ↓reduceDIte]

theorem setSize'_eq_setSize (bs : ByteArray) (size : Nat) (exact : Bool) :
    bs.setSize' size exact = Squash.mk ⟨bs.setSize size exact,
      size_setSize .., @getElem_setSize_eq_getElem bs size exact⟩ :=
  Subsingleton.allEq ..

/--
Creates an array that contains n repetitions of the byte v.
-/
def replicate (n : Nat) (v : UInt8) :=
  Quot.liftOn ((emptyWithCapacity n).setSize' n)
    (fun x => x.1.fill' 0 n v)
    (fun a b _ => by
      ext
      · simp [a.2, b.2]
      · rename_i h
        simp only [size_fill', b.2] at h
        simp [getElem_fill', h])

@[simp]
theorem _root_.Array.extract_size' {xs : Array α} {size : Nat} (h : size = xs.size) :
    xs.extract 0 size = xs := by
  rw [h, Array.extract_size]

@[simp]
theorem data_replicate (size : Nat) (value : UInt8) :
    (replicate size value).data = Array.replicate size value := by
  simp only [replicate]
  cases (emptyWithCapacity size).setSize' size using Quot.ind with | mk a => ?_
  simp [Quot.liftOn, fill', copySlice, ← size_def, Array.extract_empty_of_size_le_start, a.2]

end ByteArray
