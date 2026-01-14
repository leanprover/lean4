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
