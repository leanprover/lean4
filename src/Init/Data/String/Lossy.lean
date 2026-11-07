/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.String.Basic
public import Init.Data.String.Decode
import Init.WFTactics
import Init.Omega

namespace String

def skipContinuationBytes (b : ByteArray) (i : Nat) : Nat :=
  if h : i < b.size then
    if b[i].isUTF8ContinuationByte then
      skipContinuationBytes b (i + 1)
    else i
  else i

theorem le_skipContinuationBytes (b : ByteArray) (i : Nat) :
    i ≤ skipContinuationBytes b i := by
  fun_induction skipContinuationBytes with omega

/--
Decodes a sequence of characters from their UTF-8 representation, replacing invalid byte
sequences with `�` (`U+FFFD`, the Unicode replacement character). Whenever decoding fails at some
byte, that byte and all immediately following continuation bytes are replaced by a single `�`.

Examples:
 * `String.fromUTF8Lossy [0x4C, 0xE2, 0x88, 0x83, 0x4E].toByteArray = "L∃N"`
 * `String.fromUTF8Lossy [0x61, 0xFF, 0x62].toByteArray = "a�b"`, since `0xFF` never occurs in
   UTF-8.
 * `String.fromUTF8Lossy [0x61, 0xE2, 0x88, 0x62].toByteArray = "a�b"`, since the three-byte
   sequence starting with `0xE2` is truncated.
 * `String.fromUTF8Lossy [0x61, 0xED, 0xA0, 0x80, 0x62].toByteArray = "a�b"`, since
   `0xED 0xA0 0x80` would encode the surrogate code point `U+D800`, which is not a valid `Char`.
 * `String.fromUTF8Lossy [0x61, 0x80, 0x80, 0x80, 0x62].toByteArray = "a�b"`, since a run of
   stray continuation bytes is replaced by a single `�`.
 * `String.fromUTF8Lossy [0xFF, 0xFF].toByteArray = "��"`
-/
@[inline]
public def fromUTF8Lossy (b : ByteArray) : String :=
  go 0 ""
where
  go (i : Nat) (acc : String) : String :=
    if i < b.size then
      match b.utf8DecodeChar? i with
      | some c =>
        have := c.utf8Size_pos
        go (i + c.utf8Size) (acc.push c)
      | none =>
        have := le_skipContinuationBytes b (i + 1)
        go (skipContinuationBytes b (i + 1)) (acc.push '�')
    else acc

end String
