/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module

prelude
public import Init.Data.ByteArray.Basic
import Init.Data.String.Defs
import Init.Data.UInt.Basic

set_option doc.verso true

/--
Interprets a {name}`ByteArray` of size 8 as a little-endian {name}`UInt64`.

Panics if the array's size is not 8.
-/
public def ByteArray.toUInt64LE! (bs : ByteArray) : UInt64 :=
  assert! bs.size == 8
  (bs.get! 7).toUInt64 <<< 0x38 |||
  (bs.get! 6).toUInt64 <<< 0x30 |||
  (bs.get! 5).toUInt64 <<< 0x28 |||
  (bs.get! 4).toUInt64 <<< 0x20 |||
  (bs.get! 3).toUInt64 <<< 0x18 |||
  (bs.get! 2).toUInt64 <<< 0x10 |||
  (bs.get! 1).toUInt64 <<< 0x8  |||
  (bs.get! 0).toUInt64

/--
Interprets a {name}`ByteArray` of size 8 as a big-endian {name}`UInt64`.

Panics if the array's size is not 8.
-/
public def ByteArray.toUInt64BE! (bs : ByteArray) : UInt64 :=
  assert! bs.size == 8
  (bs.get! 0).toUInt64 <<< 0x38 |||
  (bs.get! 1).toUInt64 <<< 0x30 |||
  (bs.get! 2).toUInt64 <<< 0x28 |||
  (bs.get! 3).toUInt64 <<< 0x20 |||
  (bs.get! 4).toUInt64 <<< 0x18 |||
  (bs.get! 5).toUInt64 <<< 0x10 |||
  (bs.get! 6).toUInt64 <<< 0x8  |||
  (bs.get! 7).toUInt64

/--
Reads the little-endian {name}`UInt32` stored in the four bytes starting at byte offset {name}`i`.

The offset need not be a multiple of four.
-/
@[extern "lean_byte_array_uget_uint32_le"]
public def ByteArray.ugetUInt32LE (a : @& ByteArray) (i : USize)
    (h : i.toNat + 4 ≤ a.size := by get_elem_tactic) : UInt32 :=
  have hk {k} (hk : k < 4) : i.toNat + k < a.size := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) h
  (a[i.toNat + 0]'(hk (by decide))).toUInt32 |||
  (a[i.toNat + 1]'(hk (by decide))).toUInt32 <<< 8 |||
  (a[i.toNat + 2]'(hk (by decide))).toUInt32 <<< 16 |||
  (a[i.toNat + 3]'(hk (by decide))).toUInt32 <<< 24

/--
Stores {name}`v` in little-endian order in the four bytes starting at byte offset {name}`i`.

The offset need not be a multiple of four. The array is modified in-place if there are no other
references to it.
-/
@[extern "lean_byte_array_uset_uint32_le"]
public def ByteArray.usetUInt32LE (a : ByteArray) (i : USize) (v : UInt32)
    (_h : i.toNat + 4 ≤ a.size := by get_elem_tactic) : ByteArray :=
  a.set! i.toNat v.toUInt8 |>.set! (i.toNat + 1) (v >>> 8).toUInt8
    |>.set! (i.toNat + 2) (v >>> 16).toUInt8 |>.set! (i.toNat + 3) (v >>> 24).toUInt8

/--
Returns an array of {name}`n` bytes, each equal to {name}`v`.
-/
@[extern "lean_byte_array_replicate"]
public def ByteArray.replicate (n : @& Nat) (v : UInt8) : ByteArray :=
  ⟨Array.replicate n v⟩

/--
Returns the first {name}`n` bytes of {name}`a`, or {name}`a` itself if it has at most {name}`n`
bytes.

If there are no other references to the array, it is shrunk in-place without copying.
-/
@[extern "lean_byte_array_shrink"]
public def ByteArray.shrink (a : ByteArray) (n : @& Nat) : ByteArray :=
  a.extract 0 n
