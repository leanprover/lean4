/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.Data.ToString.Basic
import Init.Data.String.Basic
import Init.Data.Nat.Fold

namespace Lake

public def lpad (s : String) (c : Char) (len : Nat) : String :=
  "".pushn c (len - s.length) ++ s

public def rpad (s : String) (c : Char) (len : Nat) : String :=
  s.pushn c (len - s.length)

public def zpad (n : Nat) (len : Nat) : String :=
  lpad (toString n) '0' len

/-- Returns whether a string is composed of only hexadecimal digits. -/
public def isHex (s : String) : Bool :=
  s.utf8ByteSize.all fun i h =>
    let c := s.getUTF8Byte ⟨i⟩ h
    if c ≤ 57 then -- '9'
      48 ≤ c -- '0'
    else if c ≤ 102 then -- 'f'
      97 ≤ c -- 'a'
    else if c ≤ 70 then -- 'F'
      65 ≤ c -- 'A'
    else
      false

def lowerHexByte (n : UInt8) : UInt8 :=
  if n ≤ 9 then
    n + 48 -- + '0'
  else
    n + 87 -- + ('a' - 10)

theorem isValidChar_of_lt_256 (h : n < 256) : isValidChar n :=
  Or.inl <| Nat.lt_trans h (by decide)

def lowerHexChar (n : UInt8) : Char :=
  ⟨lowerHexByte n |>.toUInt32, isValidChar_of_lt_256 <|
     UInt32.lt_iff_toNat_lt.mpr <| (lowerHexByte n).toNat_lt⟩

-- TODO: use `init := String.emptyWithCapacity 16` when available
public def lowerHexUInt64 (n : UInt64) (init := "") : String :=
  init
  |>.push (lowerHexChar (n >>> 60 &&& 0xf).toUInt8)
  |>.push (lowerHexChar (n >>> 56 &&& 0xf).toUInt8)
  |>.push (lowerHexChar (n >>> 52 &&& 0xf).toUInt8)
  |>.push (lowerHexChar (n >>> 48 &&& 0xf).toUInt8)
  |>.push (lowerHexChar (n >>> 44 &&& 0xf).toUInt8)
  |>.push (lowerHexChar (n >>> 40 &&& 0xf).toUInt8)
  |>.push (lowerHexChar (n >>> 36 &&& 0xf).toUInt8)
  |>.push (lowerHexChar (n >>> 32 &&& 0xf).toUInt8)
  |>.push (lowerHexChar (n >>> 28 &&& 0xf).toUInt8)
  |>.push (lowerHexChar (n >>> 24 &&& 0xf).toUInt8)
  |>.push (lowerHexChar (n >>> 20 &&& 0xf).toUInt8)
  |>.push (lowerHexChar (n >>> 16 &&& 0xf).toUInt8)
  |>.push (lowerHexChar (n >>> 12 &&& 0xf).toUInt8)
  |>.push (lowerHexChar (n >>> 8 &&& 0xf).toUInt8)
  |>.push (lowerHexChar (n >>> 4 &&& 0xf).toUInt8)
  |>.push (lowerHexChar (n &&& 0xf).toUInt8)

-- sanity check
example : "0123456789abcdef" = lowerHexUInt64 0x0123456789abcdef := by native_decide
