/-
Copyright (c) 2026 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.UInt.Basic
public import Init.Data.BitVec.Basic
import Init.Data.UInt.Lemmas
import Init.Data.UInt.IntToBitVec
import Init.Data.BitVec.Lemmas

public section

/-! Leading- and trailing-zero counts for unsigned machine integers. -/

/--
Count the trailing zero bits, returning 8 on zero.

See `UInt8.ctz_def` for the specification via `toNat`.
-/
@[expose, extern "lean_uint8_ctz"]
def UInt8.ctz (x : UInt8) : UInt8 := ⟨x.toBitVec.ctz⟩

@[simp, int_toBitVec]
theorem UInt8.toBitVec_ctz (x : UInt8) : x.ctz.toBitVec = x.toBitVec.ctz := rfl

/-- The natural-number specification of `UInt8.ctz`. -/
theorem UInt8.toNat_ctz (x : UInt8) : x.ctz.toNat =
    if x = 0 then 8 else x.toNat.trailingZeros := by
  change x.toBitVec.ctz.toNat = _
  rw [BitVec.toNat_ctz]
  have h : x.toBitVec = 0 ↔ x = 0 := UInt8.toBitVec_inj
  simp only [h, UInt8.toNat_toBitVec]

/-- Expresses `UInt8.ctz` through its natural-number specification. -/
theorem UInt8.ctz_def (x : UInt8) :
    x.ctz = UInt8.ofNat (if x = 0 then 8 else x.toNat.trailingZeros) := by
  rw [← UInt8.toNat_ctz, UInt8.ofNat_toNat]

/--
Count the leading zero bits, returning 8 on zero.

See `UInt8.clz_def` for the specification via `toNat`.
-/
@[expose, extern "lean_uint8_clz"]
def UInt8.clz (x : UInt8) : UInt8 := ⟨x.toBitVec.clz⟩

@[simp, int_toBitVec]
theorem UInt8.toBitVec_clz (x : UInt8) : x.clz.toBitVec = x.toBitVec.clz := rfl

/-- The natural-number specification of `UInt8.clz`. -/
theorem UInt8.toNat_clz (x : UInt8) : x.clz.toNat =
    if x = 0 then 8 else 8 - (x.toNat.log2 + 1) := by
  change x.toBitVec.clz.toNat = _
  rw [BitVec.toNat_clz]
  have h : x.toBitVec = 0 ↔ x = 0 := UInt8.toBitVec_inj
  simp only [h, UInt8.toNat_toBitVec]

/-- Expresses `UInt8.clz` through its natural-number specification. -/
theorem UInt8.clz_def (x : UInt8) :
    x.clz = UInt8.ofNat (if x = 0 then 8 else 8 - (x.toNat.log2 + 1)) := by
  rw [← UInt8.toNat_clz, UInt8.ofNat_toNat]

/--
Count the trailing zero bits, returning 16 on zero.

See `UInt16.ctz_def` for the specification via `toNat`.
-/
@[expose, extern "lean_uint16_ctz"]
def UInt16.ctz (x : UInt16) : UInt16 := ⟨x.toBitVec.ctz⟩

@[simp, int_toBitVec]
theorem UInt16.toBitVec_ctz (x : UInt16) : x.ctz.toBitVec = x.toBitVec.ctz := rfl

/-- The natural-number specification of `UInt16.ctz`. -/
theorem UInt16.toNat_ctz (x : UInt16) : x.ctz.toNat =
    if x = 0 then 16 else x.toNat.trailingZeros := by
  change x.toBitVec.ctz.toNat = _
  rw [BitVec.toNat_ctz]
  have h : x.toBitVec = 0 ↔ x = 0 := UInt16.toBitVec_inj
  simp only [h, UInt16.toNat_toBitVec]

/-- Expresses `UInt16.ctz` through its natural-number specification. -/
theorem UInt16.ctz_def (x : UInt16) :
    x.ctz = UInt16.ofNat (if x = 0 then 16 else x.toNat.trailingZeros) := by
  rw [← UInt16.toNat_ctz, UInt16.ofNat_toNat]

/--
Count the leading zero bits, returning 16 on zero.

See `UInt16.clz_def` for the specification via `toNat`.
-/
@[expose, extern "lean_uint16_clz"]
def UInt16.clz (x : UInt16) : UInt16 := ⟨x.toBitVec.clz⟩

@[simp, int_toBitVec]
theorem UInt16.toBitVec_clz (x : UInt16) : x.clz.toBitVec = x.toBitVec.clz := rfl

/-- The natural-number specification of `UInt16.clz`. -/
theorem UInt16.toNat_clz (x : UInt16) : x.clz.toNat =
    if x = 0 then 16 else 16 - (x.toNat.log2 + 1) := by
  change x.toBitVec.clz.toNat = _
  rw [BitVec.toNat_clz]
  have h : x.toBitVec = 0 ↔ x = 0 := UInt16.toBitVec_inj
  simp only [h, UInt16.toNat_toBitVec]

/-- Expresses `UInt16.clz` through its natural-number specification. -/
theorem UInt16.clz_def (x : UInt16) :
    x.clz = UInt16.ofNat (if x = 0 then 16 else 16 - (x.toNat.log2 + 1)) := by
  rw [← UInt16.toNat_clz, UInt16.ofNat_toNat]

/--
Count the trailing zero bits, returning 32 on zero.

See `UInt32.ctz_def` for the specification via `toNat`.
-/
@[expose, extern "lean_uint32_ctz"]
def UInt32.ctz (x : UInt32) : UInt32 := ⟨x.toBitVec.ctz⟩

@[simp, int_toBitVec]
theorem UInt32.toBitVec_ctz (x : UInt32) : x.ctz.toBitVec = x.toBitVec.ctz := rfl

/-- The natural-number specification of `UInt32.ctz`. -/
theorem UInt32.toNat_ctz (x : UInt32) : x.ctz.toNat =
    if x = 0 then 32 else x.toNat.trailingZeros := by
  change x.toBitVec.ctz.toNat = _
  rw [BitVec.toNat_ctz]
  have h : x.toBitVec = 0 ↔ x = 0 := UInt32.toBitVec_inj
  simp only [h, UInt32.toNat_toBitVec]

/-- Expresses `UInt32.ctz` through its natural-number specification. -/
theorem UInt32.ctz_def (x : UInt32) :
    x.ctz = UInt32.ofNat (if x = 0 then 32 else x.toNat.trailingZeros) := by
  rw [← UInt32.toNat_ctz, UInt32.ofNat_toNat]

/--
Count the leading zero bits, returning 32 on zero.

See `UInt32.clz_def` for the specification via `toNat`.
-/
@[expose, extern "lean_uint32_clz"]
def UInt32.clz (x : UInt32) : UInt32 := ⟨x.toBitVec.clz⟩

@[simp, int_toBitVec]
theorem UInt32.toBitVec_clz (x : UInt32) : x.clz.toBitVec = x.toBitVec.clz := rfl

/-- The natural-number specification of `UInt32.clz`. -/
theorem UInt32.toNat_clz (x : UInt32) : x.clz.toNat =
    if x = 0 then 32 else 32 - (x.toNat.log2 + 1) := by
  change x.toBitVec.clz.toNat = _
  rw [BitVec.toNat_clz]
  have h : x.toBitVec = 0 ↔ x = 0 := UInt32.toBitVec_inj
  simp only [h, UInt32.toNat_toBitVec]

/-- Expresses `UInt32.clz` through its natural-number specification. -/
theorem UInt32.clz_def (x : UInt32) :
    x.clz = UInt32.ofNat (if x = 0 then 32 else 32 - (x.toNat.log2 + 1)) := by
  rw [← UInt32.toNat_clz, UInt32.ofNat_toNat]

/--
Count the trailing zero bits, returning 64 on zero.

See `UInt64.ctz_def` for the specification via `toNat`.
-/
@[expose, extern "lean_uint64_ctz"]
def UInt64.ctz (x : UInt64) : UInt64 := ⟨x.toBitVec.ctz⟩

@[simp, int_toBitVec]
theorem UInt64.toBitVec_ctz (x : UInt64) : x.ctz.toBitVec = x.toBitVec.ctz := rfl

/-- The natural-number specification of `UInt64.ctz`. -/
theorem UInt64.toNat_ctz (x : UInt64) : x.ctz.toNat =
    if x = 0 then 64 else x.toNat.trailingZeros := by
  change x.toBitVec.ctz.toNat = _
  rw [BitVec.toNat_ctz]
  have h : x.toBitVec = 0 ↔ x = 0 := UInt64.toBitVec_inj
  simp only [h, UInt64.toNat_toBitVec]

/-- Expresses `UInt64.ctz` through its natural-number specification. -/
theorem UInt64.ctz_def (x : UInt64) :
    x.ctz = UInt64.ofNat (if x = 0 then 64 else x.toNat.trailingZeros) := by
  rw [← UInt64.toNat_ctz, UInt64.ofNat_toNat]

/--
Count the leading zero bits, returning 64 on zero.

See `UInt64.clz_def` for the specification via `toNat`.
-/
@[expose, extern "lean_uint64_clz"]
def UInt64.clz (x : UInt64) : UInt64 := ⟨x.toBitVec.clz⟩

@[simp, int_toBitVec]
theorem UInt64.toBitVec_clz (x : UInt64) : x.clz.toBitVec = x.toBitVec.clz := rfl

/-- The natural-number specification of `UInt64.clz`. -/
theorem UInt64.toNat_clz (x : UInt64) : x.clz.toNat =
    if x = 0 then 64 else 64 - (x.toNat.log2 + 1) := by
  change x.toBitVec.clz.toNat = _
  rw [BitVec.toNat_clz]
  have h : x.toBitVec = 0 ↔ x = 0 := UInt64.toBitVec_inj
  simp only [h, UInt64.toNat_toBitVec]

/-- Expresses `UInt64.clz` through its natural-number specification. -/
theorem UInt64.clz_def (x : UInt64) :
    x.clz = UInt64.ofNat (if x = 0 then 64 else 64 - (x.toNat.log2 + 1)) := by
  rw [← UInt64.toNat_clz, UInt64.ofNat_toNat]

/--
Count the trailing zero bits, returning the platform word width on zero.

See `USize.ctz_def` for the specification via `toNat`.
-/
@[expose, extern "lean_usize_ctz"]
def USize.ctz (x : USize) : USize := ⟨x.toBitVec.ctz⟩

@[simp]
theorem USize.toBitVec_ctz (x : USize) : x.ctz.toBitVec = x.toBitVec.ctz := rfl

/-- The natural-number specification of `USize.ctz`. -/
theorem USize.toNat_ctz (x : USize) : x.ctz.toNat =
    if x = 0 then System.Platform.numBits else x.toNat.trailingZeros := by
  change x.toBitVec.ctz.toNat = _
  rw [BitVec.toNat_ctz]
  have h : x.toBitVec = 0 ↔ x = 0 := USize.toBitVec_inj
  simp only [h, USize.toNat_toBitVec]

/-- Expresses `USize.ctz` through its natural-number specification. -/
theorem USize.ctz_def (x : USize) :
    x.ctz = USize.ofNat (if x = 0 then System.Platform.numBits else x.toNat.trailingZeros) := by
  rw [← USize.toNat_ctz, USize.ofNat_toNat]

/--
Count the leading zero bits, returning the platform word width on zero.

See `USize.clz_def` for the specification via `toNat`.
-/
@[expose, extern "lean_usize_clz"]
def USize.clz (x : USize) : USize := ⟨x.toBitVec.clz⟩

@[simp]
theorem USize.toBitVec_clz (x : USize) : x.clz.toBitVec = x.toBitVec.clz := rfl

/-- The natural-number specification of `USize.clz`. -/
theorem USize.toNat_clz (x : USize) : x.clz.toNat =
    if x = 0 then System.Platform.numBits else System.Platform.numBits - (x.toNat.log2 + 1) := by
  change x.toBitVec.clz.toNat = _
  rw [BitVec.toNat_clz]
  have h : x.toBitVec = 0 ↔ x = 0 := USize.toBitVec_inj
  simp only [h, USize.toNat_toBitVec]

/-- Expresses `USize.clz` through its natural-number specification. -/
theorem USize.clz_def (x : USize) :
    x.clz = USize.ofNat (if x = 0 then System.Platform.numBits else System.Platform.numBits - (x.toNat.log2 + 1)) := by
  rw [← USize.toNat_clz, USize.ofNat_toNat]

@[int_toBitVec]
theorem USize.toBitVec32_ctz (x : USize) (h : System.Platform.numBits = 32) :
    x.ctz.toBitVec32 h = (x.toBitVec32 h).ctz := by
  simp only [USize.toBitVec32_eq_toBitVec, USize.toBitVec_ctz]
  generalize 32 = n at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec32_clz (x : USize) (h : System.Platform.numBits = 32) :
    x.clz.toBitVec32 h = (x.toBitVec32 h).clz := by
  simp only [USize.toBitVec32_eq_toBitVec, USize.toBitVec_clz]
  generalize 32 = n at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec64_ctz (x : USize) (h : System.Platform.numBits = 64) :
    x.ctz.toBitVec64 h = (x.toBitVec64 h).ctz := by
  simp only [USize.toBitVec64_eq_toBitVec, USize.toBitVec_ctz]
  generalize 64 = n at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec64_clz (x : USize) (h : System.Platform.numBits = 64) :
    x.clz.toBitVec64 h = (x.toBitVec64 h).clz := by
  simp only [USize.toBitVec64_eq_toBitVec, USize.toBitVec_clz]
  generalize 64 = n at *
  subst h
  rfl

