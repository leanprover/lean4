/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robin Arnez
-/
module

prelude
public import Init.Data.ByteArray.Basic
public import Init.Data.Array.Lemmas
public import Init.Data.UInt.Lemmas
public import Init.Data.Nat.Internal
public import Init.Grind

set_option linter.missingDocs true

public section

namespace ByteArray

/--
Interprets the value in the byte array `bs` starting at index `i`
as a 16 bit little-endian unsigned integer.
-/
@[extern "lean_byte_array_fget_uint16_le"]
def getUInt16LE (bs : @& ByteArray) (i : @& Nat)
    (h : i + 2 ≤ bs.size := by get_elem_tactic) : UInt16 :=
  let lo := bs[i]
  let hi := bs[i + 1]
  lo.toUInt16 ||| (hi.toUInt16 <<< 8)

/--
Interprets the value in the byte array `bs` starting at index `i`
as a 16 bit big-endian unsigned integer.
-/
@[extern "lean_byte_array_fget_uint16_be"]
def getUInt16BE (bs : @& ByteArray) (i : @& Nat)
    (h : i + 2 ≤ bs.size := by get_elem_tactic) : UInt16 :=
  let hi := bs[i]
  let lo := bs[i + 1]
  lo.toUInt16 ||| (hi.toUInt16 <<< 8)

/--
Interprets the value in the byte array `bs` starting at index `i`
as a 32 bit little-endian unsigned integer.
-/
@[extern "lean_byte_array_fget_uint32_le"]
def getUInt32LE (bs : @& ByteArray) (i : @& Nat)
    (h : i + 4 ≤ bs.size := by get_elem_tactic) : UInt32 :=
  let lo := bs.getUInt16LE i
  let hi := bs.getUInt16LE (i + 2)
  lo.toUInt32 ||| (hi.toUInt32 <<< 16)

/--
Interprets the value in the byte array `bs` starting at index `i`
as a 32 bit big-endian unsigned integer.
-/
@[extern "lean_byte_array_fget_uint32_be"]
def getUInt32BE (bs : @& ByteArray) (i : @& Nat)
    (h : i + 4 ≤ bs.size := by get_elem_tactic) : UInt32 :=
  let hi := bs.getUInt16BE i
  let lo := bs.getUInt16BE (i + 2)
  lo.toUInt32 ||| (hi.toUInt32 <<< 16)

/--
Interprets the value in the byte array `bs` starting at index `i`
as a 64 bit little-endian unsigned integer.
-/
@[extern "lean_byte_array_fget_uint64_le"]
def getUInt64LE (bs : @& ByteArray) (i : @& Nat)
    (h : i + 8 ≤ bs.size := by get_elem_tactic) : UInt64 :=
  let lo := bs.getUInt32LE i
  let hi := bs.getUInt32LE (i + 4)
  lo.toUInt64 ||| (hi.toUInt64 <<< 32)

/--
Interprets the value in the byte array `bs` starting at index `i`
as a 64 bit big-endian unsigned integer.
-/
@[extern "lean_byte_array_fget_uint64_be"]
def getUInt64BE (bs : @& ByteArray) (i : @& Nat)
    (h : i + 8 ≤ bs.size := by get_elem_tactic) : UInt64 :=
  let hi := bs.getUInt32BE i
  let lo := bs.getUInt32BE (i + 4)
  lo.toUInt64 ||| (hi.toUInt64 <<< 32)

@[simp, grind =]
theorem size_uset {bs : ByteArray} {i : USize} {val : UInt8} (h : i.toNat < bs.size) :
    (bs.uset i val).size = bs.size := by
  simp [size, uset]

@[simp, grind =]
theorem size_set {bs : ByteArray} {i : Nat} {val : UInt8} (h : i < bs.size) :
    (bs.set i val).size = bs.size := by
  simp [size, set]

/-- Writes the value into the byte array starting at index `i` in little-endian byte order. -/
@[extern "lean_byte_array_fset_uint16_le"]
def setUInt16LE (bs : ByteArray) (i : @& Nat) (val : UInt16)
    (h : i + 2 ≤ bs.size := by get_elem_tactic) : ByteArray :=
  let bs := bs.set i val.toUInt8
  let bs := bs.set (i + 1) (val >>> 8).toUInt8 (by grind)
  bs

@[simp, grind =]
theorem size_setUInt16LE {bs : ByteArray} {i : Nat} {val : UInt16}
    (h : i + 2 ≤ bs.size) : (bs.setUInt16LE i val).size = bs.size := by
  simp [setUInt16LE]

/-- Writes the value into the byte array starting at index `i` in big-endian byte order. -/
@[extern "lean_byte_array_fset_uint16_be"]
def setUInt16BE (bs : ByteArray) (i : @& Nat) (val : UInt16)
    (h : i + 2 ≤ bs.size := by get_elem_tactic) : ByteArray :=
  let bs := bs.set i (val >>> 8).toUInt8
  let bs := bs.set (i + 1) val.toUInt8 (by grind)
  bs

@[simp, grind =]
theorem size_setUInt16BE {bs : ByteArray} {i : Nat} {val : UInt16}
    (h : i + 2 ≤ bs.size) : (bs.setUInt16BE i val).size = bs.size := by
  simp [setUInt16BE]

/-- Writes the value into the byte array starting at index `i` in little-endian byte order. -/
@[extern "lean_byte_array_fset_uint32_le"]
def setUInt32LE (bs : ByteArray) (i : @& Nat) (val : UInt32)
    (h : i + 4 ≤ bs.size := by get_elem_tactic) : ByteArray :=
  let bs := bs.setUInt16LE i val.toUInt16
  let bs := bs.setUInt16LE (i + 2) (val >>> 16).toUInt16 (by grind)
  bs

@[simp, grind =]
theorem size_setUInt32LE {bs : ByteArray} {i : Nat} {val : UInt32}
    (h : i + 4 ≤ bs.size) : (bs.setUInt32LE i val).size = bs.size := by
  simp [setUInt32LE]

/-- Writes the value into the byte array starting at index `i` in big-endian byte order. -/
@[extern "lean_byte_array_fset_uint32_be"]
def setUInt32BE (bs : ByteArray) (i : @& Nat) (val : UInt32)
    (h : i + 4 ≤ bs.size := by get_elem_tactic) : ByteArray :=
  let bs := bs.setUInt16BE i (val >>> 16).toUInt16
  let bs := bs.setUInt16BE (i + 2) val.toUInt16 (by grind)
  bs

@[simp, grind =]
theorem size_setUInt32BE {bs : ByteArray} {i : Nat} {val : UInt32}
    (h : i + 4 ≤ bs.size) : (bs.setUInt32BE i val).size = bs.size := by
  simp [setUInt32BE]

/-- Writes the value into the byte array starting at index `i` in little-endian byte order. -/
@[extern "lean_byte_array_fset_uint64_le"]
def setUInt64LE (bs : ByteArray) (i : @& Nat) (val : UInt64)
    (h : i + 8 ≤ bs.size := by get_elem_tactic) : ByteArray :=
  let bs := bs.setUInt32LE i val.toUInt32
  let bs := bs.setUInt32LE (i + 4) (val >>> 32).toUInt32 (by grind)
  bs

@[simp, grind =]
theorem size_setUInt64LE {bs : ByteArray} {i : Nat} {val : UInt64}
    (h : i + 8 ≤ bs.size) : (bs.setUInt64LE i val).size = bs.size := by
  simp [setUInt64LE]

/-- Writes the value into the byte array starting at index `i` in big-endian byte order. -/
@[extern "lean_byte_array_fset_uint64_be"]
def setUInt64BE (bs : ByteArray) (i : @& Nat) (val : UInt64)
    (h : i + 8 ≤ bs.size := by get_elem_tactic) : ByteArray :=
  let bs := bs.setUInt32BE i (val >>> 32).toUInt32
  let bs := bs.setUInt32BE (i + 4) val.toUInt32 (by grind)
  bs

@[simp, grind =]
theorem size_setUInt64BE {bs : ByteArray} {i : Nat} {val : UInt64}
    (h : i + 8 ≤ bs.size) : (bs.setUInt64BE i val).size = bs.size := by
  simp [setUInt64BE]

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
  let prevSize := bs.size
  Quot.liftOn (setSize' bs size exact)
    (fun bs' => if h : prevSize < size then bs'.1.fill' prevSize (size - prevSize) 0 else bs'.1)
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

@[simp, grind =]
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

@[simp]
theorem size_replicate {n : Nat} {v : UInt8} : (replicate n v).size = n := by
  simp [size_def]

@[simp]
theorem getElem_replicate {i : Nat} {n : Nat} {v : UInt8} (h : i < (replicate n v).size) :
    (replicate n v)[i] = v := by
  simp [getElem_def]

-- TODO: `pushUIntN{LE/BE}`

/--
Returns true if and only if the slices `[asOff, asOff + len)` in `as` and `[bsOff, bsOff + len)` in
`bs` contain the same data.
-/
@[extern "lean_byte_array_slice_eq"]
def sliceEq' (as : @& ByteArray) (asOff : @& Nat) (bs : @& ByteArray) (bsOff len : @& Nat)
    (h : asOff + len ≤ as.size := by get_elem_tactic)
    (h' : bsOff + len ≤ bs.size := by get_elem_tactic) : Bool :=
  as.data.extract asOff (asOff + len) == bs.data.extract bsOff (bsOff + len)

/--
Returns true if and only if the slices `[asOff, asOff + len)` in `as` and `[bsOff, bsOff + len)` in
`bs` exist and contain the same data.
-/
def sliceEq (as : ByteArray) (asOff : Nat) (bs : ByteArray) (bsOff : Nat) (len : Nat) : Bool :=
  ∃ h h', sliceEq' as asOff bs bsOff len h h'

/--
Returns whether two byte arrays are equal.

The notation `==` is preferred over using this function directly.
-/
protected def beq (as bs : ByteArray) : Bool :=
  if h : as.size = bs.size then
    sliceEq' as 0 bs 0 as.size
  else
    false

protected theorem beq_iff_eq {as bs : ByteArray} : as.beq bs ↔ as = bs := by
  dsimp [ByteArray.beq]
  split
  · rename_i h
    simp [sliceEq', ← size_def, h]
    exact ⟨fun h => (h ▸ rfl : mk as.data = mk bs.data), fun h => h ▸ rfl⟩
  · rename_i h
    simp [ne_of_apply_ne size h]

instance : DecidableEq ByteArray := fun _ _ =>
  decidable_of_decidable_of_iff ByteArray.beq_iff_eq

end ByteArray
