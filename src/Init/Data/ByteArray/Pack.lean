/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.ByteArray.Basic
public import Init.Data.UInt.Basic

/-!
# Wide fixed-width integer load/store on `ByteArray`

Accessors that read and write a `UInt16` / `UInt32` / `UInt64` at a *byte* offset
of a `ByteArray`, in explicit little- or big-endian order, operating directly on
the underlying contiguous buffer rather than via an `Array UInt32` (a pointer-sized
slot per element, with an unbox on each read) or shifts-and-ors written in Lean.
The `@[extern]` implementations are portable byte assembly, which optimizing
compilers can lower to a wide (possibly unaligned) load or store.

For each width `W` and endianness `E` there are three read and three write
variants, mirroring `ByteArray.get!`/`get`/`uget` and `set!`/`set`/`uset`:

* `getUIntWE!` / `setUIntWE!` — `Nat` offset, no proof. All-or-nothing on bounds:
  a read returns `0` and a write leaves the array unchanged unless the whole
  `W/8`-byte window fits. These are the proof-level specification; the
  proof-carrying variants below are definitionally equal to them.
* `getUIntWE` / `setUIntWE` — `Nat` offset with an in-bounds proof.
* `ugetUIntWE` / `usetUIntWE` — `USize` offset with an in-bounds proof.

In a hot loop, prefer the `USize`-indexed `ugetUIntWE` / `usetUIntWE` forms: their
index is a machine word, whereas the `Nat`-indexed variants do their index
arithmetic on `Nat`, which is markedly slower.
-/

@[expose] public section

namespace ByteArray

/-! ## UInt16 -/

/-- Reads the little-endian `UInt16` at byte offset `off`, or `0` if `off + 2 > a.size`. -/
@[extern "lean_byte_array_get_uint16le"]
def getUInt16LE! (a : @& ByteArray) (off : @& Nat) : UInt16 :=
  if off + 2 ≤ a.size then
    (a.get! off).toUInt16 |||
    (a.get! (off+1)).toUInt16 <<< 0x8
  else 0

/-- Reads the big-endian `UInt16` at byte offset `off`, or `0` if `off + 2 > a.size`. -/
@[extern "lean_byte_array_get_uint16be"]
def getUInt16BE! (a : @& ByteArray) (off : @& Nat) : UInt16 :=
  if off + 2 ≤ a.size then
    (a.get! off).toUInt16 <<< 0x8 |||
    (a.get! (off+1)).toUInt16
  else 0

/-- Writes `v` as a little-endian `UInt16` at byte offset `off`; unchanged if `off + 2 > a.size`. -/
@[extern "lean_byte_array_set_uint16le"]
def setUInt16LE! (a : ByteArray) (off : @& Nat) (v : UInt16) : ByteArray :=
  if off + 2 ≤ a.size then
    (a.set! off v.toUInt8).set! (off+1) (v >>> 0x8).toUInt8
  else a

/-- Writes `v` as a big-endian `UInt16` at byte offset `off`; unchanged if `off + 2 > a.size`. -/
@[extern "lean_byte_array_set_uint16be"]
def setUInt16BE! (a : ByteArray) (off : @& Nat) (v : UInt16) : ByteArray :=
  if off + 2 ≤ a.size then
    (a.set! off (v >>> 0x8).toUInt8).set! (off+1) v.toUInt8
  else a

/-- Reads the little-endian `UInt16` at byte offset `i`. Requires the window to be in bounds. -/
@[extern "lean_byte_array_fget_uint16le"]
def getUInt16LE : (a : @& ByteArray) → (i : @& Nat) → (h : i + 2 ≤ a.size := by get_elem_tactic) → UInt16
  | a, i, _ => a.getUInt16LE! i

/-- Reads the big-endian `UInt16` at byte offset `i`. Requires the window to be in bounds. -/
@[extern "lean_byte_array_fget_uint16be"]
def getUInt16BE : (a : @& ByteArray) → (i : @& Nat) → (h : i + 2 ≤ a.size := by get_elem_tactic) → UInt16
  | a, i, _ => a.getUInt16BE! i

/-- Reads the little-endian `UInt16` at byte offset `i` (`USize`). Requires the window to be in bounds. -/
@[extern "lean_byte_array_uget_uint16le"]
def ugetUInt16LE : (a : @& ByteArray) → (i : USize) → (h : i.toNat + 2 ≤ a.size := by get_elem_tactic) → UInt16
  | a, i, _ => a.getUInt16LE! i.toNat

/-- Reads the big-endian `UInt16` at byte offset `i` (`USize`). Requires the window to be in bounds. -/
@[extern "lean_byte_array_uget_uint16be"]
def ugetUInt16BE : (a : @& ByteArray) → (i : USize) → (h : i.toNat + 2 ≤ a.size := by get_elem_tactic) → UInt16
  | a, i, _ => a.getUInt16BE! i.toNat

/-- Writes `v` as a little-endian `UInt16` at byte offset `i`. Requires the window to be in bounds. -/
@[extern "lean_byte_array_fset_uint16le"]
def setUInt16LE : (a : ByteArray) → (i : @& Nat) → (v : UInt16) → (h : i + 2 ≤ a.size := by get_elem_tactic) → ByteArray
  | a, i, v, _ => a.setUInt16LE! i v

/-- Writes `v` as a big-endian `UInt16` at byte offset `i`. Requires the window to be in bounds. -/
@[extern "lean_byte_array_fset_uint16be"]
def setUInt16BE : (a : ByteArray) → (i : @& Nat) → (v : UInt16) → (h : i + 2 ≤ a.size := by get_elem_tactic) → ByteArray
  | a, i, v, _ => a.setUInt16BE! i v

/-- Writes `v` as a little-endian `UInt16` at byte offset `i` (`USize`). Requires the window to be in bounds. -/
@[extern "lean_byte_array_uset_uint16le"]
def usetUInt16LE : (a : ByteArray) → (i : USize) → (v : UInt16) → (h : i.toNat + 2 ≤ a.size := by get_elem_tactic) → ByteArray
  | a, i, v, _ => a.setUInt16LE! i.toNat v

/-- Writes `v` as a big-endian `UInt16` at byte offset `i` (`USize`). Requires the window to be in bounds. -/
@[extern "lean_byte_array_uset_uint16be"]
def usetUInt16BE : (a : ByteArray) → (i : USize) → (v : UInt16) → (h : i.toNat + 2 ≤ a.size := by get_elem_tactic) → ByteArray
  | a, i, v, _ => a.setUInt16BE! i.toNat v

/-! ## UInt32 -/

/-- Reads the little-endian `UInt32` at byte offset `off`, or `0` if `off + 4 > a.size`. -/
@[extern "lean_byte_array_get_uint32le"]
def getUInt32LE! (a : @& ByteArray) (off : @& Nat) : UInt32 :=
  if off + 4 ≤ a.size then
    (a.get! off).toUInt32 |||
    (a.get! (off+1)).toUInt32 <<< 0x8 |||
    (a.get! (off+2)).toUInt32 <<< 0x10 |||
    (a.get! (off+3)).toUInt32 <<< 0x18
  else 0

/-- Reads the big-endian `UInt32` at byte offset `off`, or `0` if `off + 4 > a.size`. -/
@[extern "lean_byte_array_get_uint32be"]
def getUInt32BE! (a : @& ByteArray) (off : @& Nat) : UInt32 :=
  if off + 4 ≤ a.size then
    (a.get! off).toUInt32 <<< 0x18 |||
    (a.get! (off+1)).toUInt32 <<< 0x10 |||
    (a.get! (off+2)).toUInt32 <<< 0x8 |||
    (a.get! (off+3)).toUInt32
  else 0

/-- Writes `v` as a little-endian `UInt32` at byte offset `off`; unchanged if `off + 4 > a.size`. -/
@[extern "lean_byte_array_set_uint32le"]
def setUInt32LE! (a : ByteArray) (off : @& Nat) (v : UInt32) : ByteArray :=
  if off + 4 ≤ a.size then
    (((a.set! off v.toUInt8).set! (off+1) (v >>> 0x8).toUInt8).set! (off+2)
      (v >>> 0x10).toUInt8).set! (off+3) (v >>> 0x18).toUInt8
  else a

/-- Writes `v` as a big-endian `UInt32` at byte offset `off`; unchanged if `off + 4 > a.size`. -/
@[extern "lean_byte_array_set_uint32be"]
def setUInt32BE! (a : ByteArray) (off : @& Nat) (v : UInt32) : ByteArray :=
  if off + 4 ≤ a.size then
    (((a.set! off (v >>> 0x18).toUInt8).set! (off+1) (v >>> 0x10).toUInt8).set! (off+2)
      (v >>> 0x8).toUInt8).set! (off+3) v.toUInt8
  else a

/-- Reads the little-endian `UInt32` at byte offset `i`. Requires the window to be in bounds. -/
@[extern "lean_byte_array_fget_uint32le"]
def getUInt32LE : (a : @& ByteArray) → (i : @& Nat) → (h : i + 4 ≤ a.size := by get_elem_tactic) → UInt32
  | a, i, _ => a.getUInt32LE! i

/-- Reads the big-endian `UInt32` at byte offset `i`. Requires the window to be in bounds. -/
@[extern "lean_byte_array_fget_uint32be"]
def getUInt32BE : (a : @& ByteArray) → (i : @& Nat) → (h : i + 4 ≤ a.size := by get_elem_tactic) → UInt32
  | a, i, _ => a.getUInt32BE! i

/-- Reads the little-endian `UInt32` at byte offset `i` (`USize`). Requires the window to be in bounds. -/
@[extern "lean_byte_array_uget_uint32le"]
def ugetUInt32LE : (a : @& ByteArray) → (i : USize) → (h : i.toNat + 4 ≤ a.size := by get_elem_tactic) → UInt32
  | a, i, _ => a.getUInt32LE! i.toNat

/-- Reads the big-endian `UInt32` at byte offset `i` (`USize`). Requires the window to be in bounds. -/
@[extern "lean_byte_array_uget_uint32be"]
def ugetUInt32BE : (a : @& ByteArray) → (i : USize) → (h : i.toNat + 4 ≤ a.size := by get_elem_tactic) → UInt32
  | a, i, _ => a.getUInt32BE! i.toNat

/-- Writes `v` as a little-endian `UInt32` at byte offset `i`. Requires the window to be in bounds. -/
@[extern "lean_byte_array_fset_uint32le"]
def setUInt32LE : (a : ByteArray) → (i : @& Nat) → (v : UInt32) → (h : i + 4 ≤ a.size := by get_elem_tactic) → ByteArray
  | a, i, v, _ => a.setUInt32LE! i v

/-- Writes `v` as a big-endian `UInt32` at byte offset `i`. Requires the window to be in bounds. -/
@[extern "lean_byte_array_fset_uint32be"]
def setUInt32BE : (a : ByteArray) → (i : @& Nat) → (v : UInt32) → (h : i + 4 ≤ a.size := by get_elem_tactic) → ByteArray
  | a, i, v, _ => a.setUInt32BE! i v

/-- Writes `v` as a little-endian `UInt32` at byte offset `i` (`USize`). Requires the window to be in bounds. -/
@[extern "lean_byte_array_uset_uint32le"]
def usetUInt32LE : (a : ByteArray) → (i : USize) → (v : UInt32) → (h : i.toNat + 4 ≤ a.size := by get_elem_tactic) → ByteArray
  | a, i, v, _ => a.setUInt32LE! i.toNat v

/-- Writes `v` as a big-endian `UInt32` at byte offset `i` (`USize`). Requires the window to be in bounds. -/
@[extern "lean_byte_array_uset_uint32be"]
def usetUInt32BE : (a : ByteArray) → (i : USize) → (v : UInt32) → (h : i.toNat + 4 ≤ a.size := by get_elem_tactic) → ByteArray
  | a, i, v, _ => a.setUInt32BE! i.toNat v

/-! ## UInt64 -/

/-- Reads the little-endian `UInt64` at byte offset `off`, or `0` if `off + 8 > a.size`. -/
@[extern "lean_byte_array_get_uint64le"]
def getUInt64LE! (a : @& ByteArray) (off : @& Nat) : UInt64 :=
  if off + 8 ≤ a.size then
    (a.get! off).toUInt64 |||
    (a.get! (off+1)).toUInt64 <<< 0x8 |||
    (a.get! (off+2)).toUInt64 <<< 0x10 |||
    (a.get! (off+3)).toUInt64 <<< 0x18 |||
    (a.get! (off+4)).toUInt64 <<< 0x20 |||
    (a.get! (off+5)).toUInt64 <<< 0x28 |||
    (a.get! (off+6)).toUInt64 <<< 0x30 |||
    (a.get! (off+7)).toUInt64 <<< 0x38
  else 0

/-- Reads the big-endian `UInt64` at byte offset `off`, or `0` if `off + 8 > a.size`. -/
@[extern "lean_byte_array_get_uint64be"]
def getUInt64BE! (a : @& ByteArray) (off : @& Nat) : UInt64 :=
  if off + 8 ≤ a.size then
    (a.get! off).toUInt64 <<< 0x38 |||
    (a.get! (off+1)).toUInt64 <<< 0x30 |||
    (a.get! (off+2)).toUInt64 <<< 0x28 |||
    (a.get! (off+3)).toUInt64 <<< 0x20 |||
    (a.get! (off+4)).toUInt64 <<< 0x18 |||
    (a.get! (off+5)).toUInt64 <<< 0x10 |||
    (a.get! (off+6)).toUInt64 <<< 0x8 |||
    (a.get! (off+7)).toUInt64
  else 0

/-- Writes `v` as a little-endian `UInt64` at byte offset `off`; unchanged if `off + 8 > a.size`. -/
@[extern "lean_byte_array_set_uint64le"]
def setUInt64LE! (a : ByteArray) (off : @& Nat) (v : UInt64) : ByteArray :=
  if off + 8 ≤ a.size then
    (((((((a.set! off v.toUInt8).set! (off+1) (v >>> 0x8).toUInt8).set! (off+2)
      (v >>> 0x10).toUInt8).set! (off+3) (v >>> 0x18).toUInt8).set! (off+4)
      (v >>> 0x20).toUInt8).set! (off+5) (v >>> 0x28).toUInt8).set! (off+6)
      (v >>> 0x30).toUInt8).set! (off+7) (v >>> 0x38).toUInt8
  else a

/-- Writes `v` as a big-endian `UInt64` at byte offset `off`; unchanged if `off + 8 > a.size`. -/
@[extern "lean_byte_array_set_uint64be"]
def setUInt64BE! (a : ByteArray) (off : @& Nat) (v : UInt64) : ByteArray :=
  if off + 8 ≤ a.size then
    (((((((a.set! off (v >>> 0x38).toUInt8).set! (off+1) (v >>> 0x30).toUInt8).set! (off+2)
      (v >>> 0x28).toUInt8).set! (off+3) (v >>> 0x20).toUInt8).set! (off+4)
      (v >>> 0x18).toUInt8).set! (off+5) (v >>> 0x10).toUInt8).set! (off+6)
      (v >>> 0x8).toUInt8).set! (off+7) v.toUInt8
  else a

/-- Reads the little-endian `UInt64` at byte offset `i`. Requires the window to be in bounds. -/
@[extern "lean_byte_array_fget_uint64le"]
def getUInt64LE : (a : @& ByteArray) → (i : @& Nat) → (h : i + 8 ≤ a.size := by get_elem_tactic) → UInt64
  | a, i, _ => a.getUInt64LE! i

/-- Reads the big-endian `UInt64` at byte offset `i`. Requires the window to be in bounds. -/
@[extern "lean_byte_array_fget_uint64be"]
def getUInt64BE : (a : @& ByteArray) → (i : @& Nat) → (h : i + 8 ≤ a.size := by get_elem_tactic) → UInt64
  | a, i, _ => a.getUInt64BE! i

/-- Reads the little-endian `UInt64` at byte offset `i` (`USize`). Requires the window to be in bounds. -/
@[extern "lean_byte_array_uget_uint64le"]
def ugetUInt64LE : (a : @& ByteArray) → (i : USize) → (h : i.toNat + 8 ≤ a.size := by get_elem_tactic) → UInt64
  | a, i, _ => a.getUInt64LE! i.toNat

/-- Reads the big-endian `UInt64` at byte offset `i` (`USize`). Requires the window to be in bounds. -/
@[extern "lean_byte_array_uget_uint64be"]
def ugetUInt64BE : (a : @& ByteArray) → (i : USize) → (h : i.toNat + 8 ≤ a.size := by get_elem_tactic) → UInt64
  | a, i, _ => a.getUInt64BE! i.toNat

/-- Writes `v` as a little-endian `UInt64` at byte offset `i`. Requires the window to be in bounds. -/
@[extern "lean_byte_array_fset_uint64le"]
def setUInt64LE : (a : ByteArray) → (i : @& Nat) → (v : UInt64) → (h : i + 8 ≤ a.size := by get_elem_tactic) → ByteArray
  | a, i, v, _ => a.setUInt64LE! i v

/-- Writes `v` as a big-endian `UInt64` at byte offset `i`. Requires the window to be in bounds. -/
@[extern "lean_byte_array_fset_uint64be"]
def setUInt64BE : (a : ByteArray) → (i : @& Nat) → (v : UInt64) → (h : i + 8 ≤ a.size := by get_elem_tactic) → ByteArray
  | a, i, v, _ => a.setUInt64BE! i v

/-- Writes `v` as a little-endian `UInt64` at byte offset `i` (`USize`). Requires the window to be in bounds. -/
@[extern "lean_byte_array_uset_uint64le"]
def usetUInt64LE : (a : ByteArray) → (i : USize) → (v : UInt64) → (h : i.toNat + 8 ≤ a.size := by get_elem_tactic) → ByteArray
  | a, i, v, _ => a.setUInt64LE! i.toNat v

/-- Writes `v` as a big-endian `UInt64` at byte offset `i` (`USize`). Requires the window to be in bounds. -/
@[extern "lean_byte_array_uset_uint64be"]
def usetUInt64BE : (a : ByteArray) → (i : USize) → (v : UInt64) → (h : i.toNat + 8 ≤ a.size := by get_elem_tactic) → ByteArray
  | a, i, v, _ => a.setUInt64BE! i.toNat v

end ByteArray
