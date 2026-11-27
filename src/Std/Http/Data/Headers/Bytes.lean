/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.String.Basic
public import Std.Http.Internal.Char
import Init.Omega

public section

/-!
# Byte scans on strings

Loops over the UTF-8 bytes of a string, without decoding characters, for the header fast paths that
look for ASCII delimiters (`,`, `:`, `.`) and digits.
-/

namespace Std.Http.Internal.Bytes

set_option linter.all true

open Std.Http.Internal.Char

/--
Whether every byte of `s` from position `i` on satisfies `p`.
-/
@[specialize]
def allFrom (p : UInt8 → Bool) (s : String) (i : Nat) : Bool :=
  if h : i < s.utf8ByteSize then p (s.getUTF8Byte ⟨i⟩ h) && allFrom p s (i + 1) else true
termination_by s.utf8ByteSize - i

/--
Whether every byte of `s` satisfies `p`.
-/
@[inline]
def all (p : UInt8 → Bool) (s : String) : Bool :=
  allFrom p s 0

/-- `tchar` on a byte. -/
@[inline] def isTchar (b : UInt8) : Bool := tchar (Char.ofUInt8 b)

/-- Whether a byte is not ASCII whitespace (`Char.isWhitespace`). -/
@[inline] def isNotWhitespace (b : UInt8) : Bool := !(Char.ofUInt8 b).isWhitespace

/--
The byte of `s` at position `i`, or `0` past its end.
-/
@[inline]
def get (s : String) (i : Nat) : UInt8 :=
  if h : i < s.utf8ByteSize then s.getUTF8Byte ⟨i⟩ h else 0

/--
The position after the run of ASCII whitespace (`Char.isWhitespace`) of `s` that starts at `i`,
stopping at `stop`.
-/
def skipWhitespace (s : String) (i stop : Nat) : Nat :=
  if i < stop ∧ i < s.utf8ByteSize then
    if isNotWhitespace (get s i) then i else skipWhitespace s (i + 1) stop
  else
    i
termination_by stop - i

/--
The start of the run of ASCII whitespace (`Char.isWhitespace`) of `s` that ends at `j`, stopping at
`start`.
-/
def skipWhitespaceBack (s : String) (start j : Nat) : Nat :=
  if start < j then
    if isNotWhitespace (get s (j - 1)) then j else skipWhitespaceBack s start (j - 1)
  else
    j
termination_by j

/--
The position of the first byte `b` of `s` at or after `i`, or `s.utf8ByteSize` if there is none.
-/
def findByte (s : String) (b : UInt8) (i : Nat) : Nat :=
  if h : i < s.utf8ByteSize then
    if s.getUTF8Byte ⟨i⟩ h == b then i else findByte s b (i + 1)
  else
    s.utf8ByteSize
termination_by s.utf8ByteSize - i

/--
A byte `findByte` finds is at or after where the search started.
-/
theorem le_findByte {s : String} {b : UInt8} {i : Nat} (h : findByte s b i < s.utf8ByteSize) :
    i ≤ findByte s b i := by
  fun_induction findByte s b i with
  | case1 => exact Nat.le_refl _
  | case2 i _ _ ih => exact Nat.le_trans (Nat.le_succ i) (ih h)
  | case3 => exact absurd h (Nat.lt_irrefl _)

/--
Whether every byte of `s` from `i` to `j` satisfies `p`.
-/
@[specialize]
def allBetween (p : UInt8 → Bool) (s : String) (i j : Nat) : Bool :=
  if i < j then p (get s i) && allBetween p s (i + 1) j else true
termination_by j - i

/--
The position after the run of `0` bytes of `s` that starts at `i`, stopping at `stop`.
-/
def skipZeros (s : String) (i stop : Nat) : Nat :=
  if i < stop then
    if get s i == '0'.toUInt8 then skipZeros s (i + 1) stop else i
  else
    i
termination_by stop - i

/--
The position after the last byte `b` of `s` between `start` and `j`, or `start` if there is none.
-/
def findLastByte (s : String) (b : UInt8) (start j : Nat) : Nat :=
  if start < j then
    if get s (j - 1) == b then j else findLastByte s b start (j - 1)
  else
    start
termination_by j

end Std.Http.Internal.Bytes
