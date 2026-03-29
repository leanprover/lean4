/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robin Arnez
-/
module

prelude
public import Init.Data.ByteArray.Basic
import Init.Data.ByteArray.Lemmas
import Init.Data.Array.Bootstrap
import Init.Data.Array.Lemmas
import Init.Omega
import Init.ByCases

@[expose] public section

namespace ByteArray

@[deprecated getUInt64LE! (since := "2026-03-29")]
def ByteArray.toUInt64LE! (bs : ByteArray) : UInt64 :=
  bs.getUInt64LE! 0

@[deprecated getUInt64BE! (since := "2026-03-29")]
def ByteArray.toUInt64BE! (bs : ByteArray) : UInt64 :=
  bs.getUInt64BE! 0

def SetSizeResult.setoid (origSz sz : Nat) : Setoid { x : ByteArray // x.size = sz } where
  r a b := ∀ (i : Nat) (hi : i < sz) (hi' : i < origSz), a.1[i] = b.1[i]
  iseqv := {
    refl _ _ _ _ := rfl
    symm h i hi hi' := (h i hi hi').symm
    trans h h' i hi hi' := (h i hi hi').trans (h' i hi hi')
  }

/--
A byte array of size `sz` where only the first `origSize` bytes are defined and the others are
quotiented out.
-/
structure SetSizeResult (origSz sz : Nat) where
  mk' :: value : Quotient (SetSizeResult.setoid origSz sz)

def SetSizeResult.mk {origSz sz : Nat} (bs : ByteArray) (h : bs.size = sz) :
    SetSizeResult origSz sz := ⟨Quotient.mk _ ⟨bs, h⟩⟩

/--
Low-level function for growing or shrinking a byte array. Note that the contents of the bytes
starting at index `size` are undefined when growing.

If `exact` is `false`, the capacity will be doubled when grown.
-/
@[extern "lean_byte_array_set_size"]
def setSize (bs : ByteArray) (size : @& Nat) (origSz : @& Nat) (h : bs.size = origSz)
    (exact : Bool := false) : SetSizeResult origSz size :=
  .mk ⟨bs.data.take size ++ Array.replicate (size - bs.size) 0⟩ (by simp [← size_data]; omega)

@[elab_as_elim, induction_eliminator]
theorem SetSizeResult.ind {origSz sz : Nat} {motive : SetSizeResult origSz sz → Prop}
    (mk : ∀ b hb, motive (mk b hb)) (t : SetSizeResult origSz sz) : motive t := by
  rcases t with ⟨x, hx⟩; apply mk

theorem SetSizeResult.sound {origSz sz : Nat} {a ha b hb}
    (h : ∀ i (hi : i < sz) (hi' : i < origSz), a[i] = b[i]) : @mk origSz sz a ha = mk b hb := by
  simp only [mk, mk'.injEq]
  exact Quotient.sound h

@[inline]
def SetSizeResult.lift {origSz sz : Nat} {α : Sort u} (f : (b : ByteArray) → b.size = sz → α)
    (h : ∀ a ha b hb, (∀ i (hi : i < sz) (hi' : i < origSz), a[i] = b[i]) → f a ha = f b hb)
    (x : SetSizeResult origSz sz) : α :=
  x.value.lift (fun ⟨b, hb⟩ => f b hb) (fun ⟨a, ha⟩ ⟨b, hb⟩ => h a ha b hb)

@[simp]
theorem SetSizeResult.lift_mk {origSz sz : Nat} {α : Sort u} {f h} {b hb} :
    @lift origSz sz α f h (mk b hb) = f b hb := rfl

@[inline]
def SetSizeResult.get {origSz sz : Nat} (x : SetSizeResult origSz sz) (i : Nat)
    (hi : i < sz) (hi' : i < origSz) : UInt8 :=
  x.lift (fun b _ => b[i]) fun _ _ _ _ hab => hab i hi hi'

instance : GetElem (SetSizeResult origSz sz) Nat UInt8 (fun _ i => i < sz ∧ i < origSz) where
  getElem x i h := x.get i h.1 h.2

@[simp]
theorem SetSizeResult.getElem_mk {i : Nat} {hi} :
    (@mk origSz sz b hb)[i]'hi = b[i] := rfl

@[simp]
theorem SetSizeResult.getElem_setSize {b : ByteArray} {sz origSz h exact} {i : Nat} (hi) :
    (b.setSize sz origSz h exact)[i]'hi = b[i] := by
  rw [setSize]
  simp only [Array.take_eq_extract, getElem_mk, getElem_eq_getElem_data]
  rw [Array.getElem_append_left (by simp; omega)]
  simp; rfl

/-- Given the knowledge that `sz ≤ origSz`, extract the byte array out of `x`. -/
@[inline]
def SetSizeResult.toByteArrayOfLe (x : SetSizeResult origSz sz) (h : sz ≤ origSz) : ByteArray :=
  x.lift (fun b _ => b) ?_
where finally
  intro a ha b hb hab
  dsimp only
  ext i hi
  · simp [ha, hb]
  · apply hab
    · exact ha ▸ hi
    · exact Nat.lt_of_lt_of_le (ha ▸ hi) h

@[simp]
theorem SetSizeResult.size_toByteArrayOfLe {x : SetSizeResult origSz sz} (h) :
    (x.toByteArrayOfLe h).size = sz := by
  induction x with | _ x hx; exact hx

@[simp]
theorem SetSizeResult.getElem_toByteArrayOfLe
    {x : SetSizeResult origSz sz} {h} {i : Nat} (hi) :
    (x.toByteArrayOfLe h)[i]'hi = x[i]'(by simp at hi; omega) := by
  induction x; rfl

/-- Returns all the defined bytes in `x`, i.e. the first `min origSz sz` bytes. -/
def SetSizeResult.toByteArray (x : SetSizeResult origSz sz) : ByteArray :=
  x.lift (fun b hb => (b.setSize (min origSz sz) _ hb).toByteArrayOfLe (by omega)) ?_
where finally
  intro a ha b hb hab
  dsimp only
  apply ext_getElem
  · simp
  · simp only [size_toByteArrayOfLe, getElem_toByteArrayOfLe, getElem_setSize]
    intro i h _
    exact hab i (by omega) (by omega)

@[inline]
def SetSizeResult.push (x : SetSizeResult origSz sz) (b : UInt8)
    (h : origSz < sz := by get_elem_tactic) : SetSizeResult (origSz + 1) sz :=
  x.lift (fun x _ => mk (x.set origSz b) (by simp [*])) ?_
where finally
  intro a ha b hb hab
  apply sound
  simp +contextual [Nat.lt_add_one_iff_lt_or_eq, or_imp, getElem_set, Nat.ne_of_gt, hab]

private theorem SetSizeResult.pushBitVecLE_aux (h : origSz + nbytes ≤ sz)
    (a : ByteArray) (ha : a.size = sz) (b : ByteArray) (hb : b.size = sz)
    (hab : ∀ (i : Nat) (hi : i < sz), i < origSz → a[i] = b[i]) :
    @mk (origSz + nbytes) sz (a.setBitVecLE origSz nbytes val) (by simpa using ha) =
      mk (b.setBitVecLE origSz nbytes val) (by simpa using hb) := by
  apply sound
  intro i hi hi'
  by_cases h : i < origSz
  · simpa [getElem_setBitVecLE, Nat.not_le_of_lt h] using hab i hi h
  · simp [getElem_setBitVecLE, hi', Nat.le_of_not_lt h]

private theorem SetSizeResult.pushBitVecBE_aux (h : origSz + nbytes ≤ sz)
    (a : ByteArray) (ha : a.size = sz) (b : ByteArray) (hb : b.size = sz)
    (hab : ∀ (i : Nat) (hi : i < sz), i < origSz → a[i] = b[i]) :
    @mk (origSz + nbytes) sz (a.setBitVecBE origSz nbytes val) (by simpa using ha) =
      mk (b.setBitVecBE origSz nbytes val) (by simpa using hb) := by
  apply sound
  intro i hi hi'
  by_cases h : i < origSz
  · simpa [getElem_setBitVecBE, Nat.not_le_of_lt h] using hab i hi h
  · simp [getElem_setBitVecBE, hi', Nat.le_of_not_lt h]

@[inline]
def SetSizeResult.pushBitVecLE (x : SetSizeResult origSz sz) (nbytes : Nat)
    (val : BitVec (8 * nbytes)) (h : origSz + nbytes ≤ sz := by get_elem_tactic) :
    SetSizeResult (origSz + nbytes) sz :=
  x.lift (fun x _ => mk (x.setBitVecLE origSz nbytes val) (by simp [*])) (by apply pushBitVecLE_aux h)

@[inline]
def SetSizeResult.pushBitVecBE (x : SetSizeResult origSz sz) (nbytes : Nat)
    (val : BitVec (8 * nbytes)) (h : origSz + nbytes ≤ sz := by get_elem_tactic) :
    SetSizeResult (origSz + nbytes) sz :=
  x.lift (fun x _ => mk (x.setBitVecBE origSz nbytes val) (by simp [*])) (by apply pushBitVecBE_aux h)

@[inline]
def SetSizeResult.pushUInt16LE (x : SetSizeResult origSz sz) (val : UInt16)
    (h : origSz + 2 ≤ sz := by get_elem_tactic) : SetSizeResult (origSz + 2) sz :=
  x.lift (fun x _ => mk (x.setUInt16LE origSz val) (by simp [*])) (by apply pushBitVecLE_aux h)

@[inline]
def SetSizeResult.pushUInt16BE (x : SetSizeResult origSz sz) (val : UInt16)
    (h : origSz + 2 ≤ sz := by get_elem_tactic) : SetSizeResult (origSz + 2) sz :=
  x.lift (fun x _ => mk (x.setUInt16BE origSz val) (by simp [*])) (by apply pushBitVecBE_aux h)

@[inline]
def SetSizeResult.pushUInt32LE (x : SetSizeResult origSz sz) (val : UInt32)
    (h : origSz + 4 ≤ sz := by get_elem_tactic) : SetSizeResult (origSz + 4) sz :=
  x.lift (fun x _ => mk (x.setUInt32LE origSz val) (by simp [*])) (by apply pushBitVecLE_aux h)

@[inline]
def SetSizeResult.pushUInt32BE (x : SetSizeResult origSz sz) (val : UInt32)
    (h : origSz + 4 ≤ sz := by get_elem_tactic) : SetSizeResult (origSz + 4) sz :=
  x.lift (fun x _ => mk (x.setUInt32BE origSz val) (by simp [*])) (by apply pushBitVecBE_aux h)

@[inline]
def SetSizeResult.pushUInt64LE (x : SetSizeResult origSz sz) (val : UInt64)
    (h : origSz + 8 ≤ sz := by get_elem_tactic) : SetSizeResult (origSz + 8) sz :=
  x.lift (fun x _ => mk (x.setUInt64LE origSz val) (by simp [*])) (by apply pushBitVecLE_aux h)

@[inline]
def SetSizeResult.pushUInt64BE (x : SetSizeResult origSz sz) (val : UInt64)
    (h : origSz + 8 ≤ sz := by get_elem_tactic) : SetSizeResult (origSz + 8) sz :=
  x.lift (fun x _ => mk (x.setUInt64BE origSz val) (by simp [*])) (by apply pushBitVecBE_aux h)

def pushBitVecLE (x : ByteArray) (nbytes : Nat) (val : BitVec (8 * nbytes)) : ByteArray :=
  let origSz := x.size
  ((x.setSize (origSz + nbytes) origSz rfl).pushBitVecLE nbytes val).toByteArrayOfLe (Nat.le_refl _)

def pushBitVecBE (x : ByteArray) (nbytes : Nat) (val : BitVec (8 * nbytes)) : ByteArray :=
  let origSz := x.size
  ((x.setSize (origSz + nbytes) origSz rfl).pushBitVecBE nbytes val).toByteArrayOfLe (Nat.le_refl _)

def pushUInt16LE (x : ByteArray) (val : UInt16) : ByteArray :=
  let origSz := x.size
  ((x.setSize (origSz + 2) origSz rfl).pushUInt16LE val).toByteArrayOfLe (Nat.le_refl _)

def pushUInt16BE (x : ByteArray) (val : UInt16) : ByteArray :=
  let origSz := x.size
  ((x.setSize (origSz + 2) origSz rfl).pushUInt16BE val).toByteArrayOfLe (Nat.le_refl _)

def pushUInt32LE (x : ByteArray) (val : UInt32) : ByteArray :=
  let origSz := x.size
  ((x.setSize (origSz + 4) origSz rfl).pushUInt32LE val).toByteArrayOfLe (Nat.le_refl _)

def pushUInt32BE (x : ByteArray) (val : UInt32) : ByteArray :=
  let origSz := x.size
  ((x.setSize (origSz + 4) origSz rfl).pushUInt32BE val).toByteArrayOfLe (Nat.le_refl _)

def pushUInt64LE (x : ByteArray) (val : UInt64) : ByteArray :=
  let origSz := x.size
  ((x.setSize (origSz + 8) origSz rfl).pushUInt64LE val).toByteArrayOfLe (Nat.le_refl _)

def pushUInt64BE (x : ByteArray) (val : UInt64) : ByteArray :=
  let origSz := x.size
  ((x.setSize (origSz + 8) origSz rfl).pushUInt64BE val).toByteArrayOfLe (Nat.le_refl _)

@[inline]
def SetSizeResult.fill (x : SetSizeResult origSz sz) (b : UInt8) (h : origSz ≤ sz) :
    ByteArray :=
  x.lift (fun x _ => x.fill origSz (sz - origSz) b) ?_
where finally
  intro a ha b hb hab
  dsimp only
  apply ext_getElem
  · simp [ha, hb]
  · intro i hi hi'
    simp only [size_fill, ha] at hi
    simp only [getElem_fill, Nat.add_sub_cancel' h, hi, and_true]
    split
    · rfl
    · apply hab <;> omega

@[simp]
theorem SetSizeResult.size_fill {x : SetSizeResult origSz sz} {b h} :
    (x.fill b h).size = sz := by
  induction x with | _ x hx
  simpa [fill] using hx

theorem SetSizeResult.getElem_fill {x : SetSizeResult origSz sz} {b h} {i : Nat} {hi} :
    (x.fill b h)[i]'hi = if h : i < origSz then x[i]'⟨by simpa using hi, h⟩ else b := by
  induction x with | _ x hx
  simp only [size_fill] at hi
  simp [fill, ByteArray.getElem_fill, Nat.add_sub_cancel' h, hi, ← Nat.not_lt]; rfl

def setSizeD (bs : ByteArray) (size : Nat) (exact : Bool := false) : ByteArray :=
  let prevSz := bs.size
  let res := bs.setSize size prevSz rfl exact
  if h : prevSz < size then res.fill 0 (Nat.le_of_lt h) else res.toByteArrayOfLe (Nat.not_lt.mp h)

@[simp, grind =]
theorem size_setSizeD (bs : ByteArray) (size : Nat) (exact : Bool) :
    (bs.setSizeD size exact).size = size := by
  rw [setSizeD]
  split <;> simp

@[grind =]
theorem getElem_setSizeD {bs : ByteArray} {size : Nat} {exact : Bool} {i : Nat}
    (h : i < (bs.setSizeD size exact).size) :
    (bs.setSizeD size exact)[i] = if h : i < bs.size then bs[i] else 0 := by
  rw [size_setSizeD] at h
  simp only [setSizeD]
  split
  · simp [SetSizeResult.getElem_fill]
  · rw [dif_pos (c := i < _) (by omega)]
    simp

/-- Creates an array that contains n repetitions of the byte v. -/
def replicate (n : Nat) (v : UInt8) :=
  ((emptyWithCapacity n).setSize n 0 rfl).fill v (by simp)

@[simp]
theorem data_replicate (size : Nat) (value : UInt8) :
    (replicate size value).data = Array.replicate size value := by
  simp only [replicate]
  ext
  · simp
  · simp [← getElem_eq_getElem_data, SetSizeResult.getElem_fill]

@[simp]
theorem size_replicate {n : Nat} {v : UInt8} : (replicate n v).size = n := by
  simp [← size_data]

@[simp]
theorem getElem_replicate {i : Nat} {n : Nat} {v : UInt8} (h : i < (replicate n v).size) :
    (replicate n v)[i] = v := by
  simp [getElem_eq_getElem_data]

end ByteArray
