/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
import Init.Grind
import Init.While
import Init.Data.SInt.Lemmas
import Init.Data.UInt.Lemmas
import Init.Data.UInt.Bitwise
import Init.Data.Array.Lemmas
public import Init.Data.String.Basic
public import Std.Http.Internal.Char

public section

/-!
# URI Encoding

This module provides utilities for percent-encoding URI components according to RFC 3986. It includes
character validation, encoding/decoding functions, and types that maintain encoding invariants through
Lean's dependent type system.

Reference: https://www.rfc-editor.org/rfc/rfc3986.html#section-2.1
-/

namespace Std.Http.URI

set_option linter.all true

open Http.Internal Char

/--
Checks if a byte is a valid character in a percent-encoded URI component. Valid characters are
unreserved characters or the percent sign (for escape sequences).
-/
def isEncodedChar (rule : UInt8 → Bool) (c : UInt8) : Bool :=
  isAsciiByte c ∧ (rule c ∨ isHexDigitByte c ∨ c = '%'.toUInt8)

/--
Checks if a byte is valid in a percent-encoded query string component. Extends `isEncodedChar` to also
allow '+', which RFC 3986 admits anywhere in a query as a sub-delim, even under a narrower rule.
-/
def isEncodedQueryChar (rule : UInt8 → Bool) (c : UInt8) : Bool :=
  isEncodedChar rule c ∨ c = '+'.toUInt8

/--
Checks if all characters in a `ByteArray` are allowed in an encoded URI component. This is a fast check
that only verifies the character set, not full encoding validity.
-/
@[inline]
abbrev IsAllowedEncodedChars (rule : UInt8 → Bool) (s : ByteArray) : Prop :=
  s.data.all (isEncodedChar rule)

instance : Decidable (IsAllowedEncodedChars r s) :=
  inferInstanceAs (Decidable (s.data.all (isEncodedChar r) = true))

/--
Checks if all characters in a `ByteArray` are allowed in an encoded query parameter. Allows '+' as an
ordinary sub-delim.
-/
@[inline]
abbrev IsAllowedEncodedQueryChars (rule : UInt8 → Bool) (s : ByteArray) : Prop :=
  s.data.all (isEncodedQueryChar rule)

instance : Decidable (IsAllowedEncodedQueryChars r s) :=
  inferInstanceAs (Decidable (s.data.all (isEncodedQueryChar r) = true))

/--
Validates that all percent signs in a byte array are followed by exactly two hexadecimal digits.
This ensures proper percent-encoding according to RFC 3986.

For example:
- `%20` is valid (percent followed by two hex digits)
- `%` is invalid (percent with no following digits)
- `%2` is invalid (percent followed by only one digit)
- `%GG` is invalid (percent followed by non-hex characters)
-/
def isValidPercentEncoding (ba : ByteArray) : Bool :=
  let rec loop (i : Nat) : Bool :=
    if h : i < ba.size then
      let c := ba[i]'h
      if c = '%'.toUInt8 then
          if h₂ : i + 2 < ba.size then
            let d1 := ba[i + 1]'(by omega)
            let d2 := ba[i + 2]'h₂
            if isHexDigitByte d1 && isHexDigitByte d2 then
              loop (i + 3)
          else false
        else false
      else loop (i + 1)
    else true
  termination_by ba.size - i
  loop 0

/--
Converts a nibble (4-bit value, 0-15) to its hexadecimal digit representation. Returns '0'-'9' for
values 0-9, and 'A'-'F' for values 10-15.
-/
def hexDigit (n : UInt8) : UInt8 :=
  if n < 10 then (n + '0'.toUInt8)
  else (n - 10 + 'A'.toUInt8)

/--
Converts a hexadecimal digit character to its numeric value (0-15).
Returns `none` if the character is not a valid hex digit.
-/
def hexDigitToUInt8? (c : UInt8) : Option UInt8 :=
  if c ≥ '0'.toUInt8 && c ≤ '9'.toUInt8 then
    some (c - '0'.toUInt8)
  else if c ≥ 'a'.toUInt8 && c ≤ 'f'.toUInt8 then
    some (c - 'a'.toUInt8 + 10)
  else if c ≥ 'A'.toUInt8 && c ≤ 'F'.toUInt8 then
    some (c - 'A'.toUInt8 + 10)
  else
    none

private theorem IsAllowedEncodedChars.push {bs : ByteArray} (h : IsAllowedEncodedChars r bs) (h₁ : isEncodedChar r c) :
    IsAllowedEncodedChars r (bs.push c) := by
  simpa [IsAllowedEncodedChars, ByteArray.push, Array.all_push, And.intro h h₁]

private theorem IsAllowedEncodedQueryChars.push {bs : ByteArray} (h : IsAllowedEncodedQueryChars r bs) (h₁ : isEncodedQueryChar r c) :
    IsAllowedEncodedQueryChars r (bs.push c) := by
  simpa [IsAllowedEncodedQueryChars, ByteArray.push, Array.all_push, And.intro h h₁]

private theorem isEncodedChar_isAscii (c : UInt8) (h : isEncodedChar r c) : isAsciiByte c := by
  simp [isEncodedChar, isAsciiByte] at *
  exact h.left

private theorem isEncodedQueryChar_isAscii (c : UInt8) (h : isEncodedQueryChar r c) : isAsciiByte c := by
  unfold isEncodedQueryChar isAsciiByte at *
  simp at h
  rcases h
  next h => exact isEncodedChar_isAscii c h
  next h => subst_vars; decide

private theorem hexDigit_isHexDigit (h₀ : x < 16) : isHexDigitByte (hexDigit x) := by
  unfold hexDigit isHexDigitByte
  have h₁ : x.toNat < 16 := h₀
  split <;> simp

  next p =>
    have h₂ : x.toNat < 10 := p
    have h₂ : 48 ≤ x.toNat + 48 := by omega
    have h₃ : x.toNat + 48 ≤ 57 := by omega
    have h₄ : x.toNat + 48 < 256 := by omega

    refine Or.inl (Or.inl ⟨?_, ?_⟩)
    · exact (UInt8.ofNat_le_iff_le (by decide) h₄ |>.mpr h₂)
    · exact (UInt8.ofNat_le_iff_le h₄ (by decide) |>.mpr h₃)

  next p =>
    have h₂ : ¬(x.toNat < 10) := p
    have h₃ : 65 ≤ x.toNat - 10 + 65 := by omega
    have h₅ : x.toNat - 10 + 65 ≤ 70 := by omega
    have h₄ : x.toNat - 10 + 65 < 256 := by omega

    refine Or.inr ⟨?_, ?_⟩
    · simpa [UInt8.ofNat_sub (by omega : 10 ≤ x.toNat)] using!
        UInt8.ofNat_le_iff_le (by decide : 65 < 256) h₄ |>.mpr h₃
    · simpa [UInt8.ofNat_add, UInt8.ofNat_sub (by omega : 10 ≤ x.toNat)] using!
        UInt8.ofNat_le_iff_le h₄ (by decide : 70 < 256) |>.mpr h₅

private theorem isHexDigit_isAscii {c : UInt8} (h : isHexDigitByte c) : isAsciiByte c := by
  simp [isHexDigitByte, isAsciiByte] at *
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact UInt8.lt_of_le_of_lt h2 (by decide)
  next h => exact UInt8.lt_of_le_of_lt h.right (by decide)
  · exact UInt8.lt_of_le_of_lt h2 (by decide)

private theorem isHexDigit_isEncodedChar {c : UInt8} (h : isHexDigitByte c) : isEncodedChar r c := by
  unfold isEncodedChar
  simp at *
  exact And.intro (isHexDigit_isAscii h) (Or.inr (Or.inl h))

private theorem isHexDigit_isEncodedQueryChar {c : UInt8} (h : isHexDigitByte c) : isEncodedQueryChar r c := by
  unfold isEncodedQueryChar isEncodedChar
  simp at *
  exact Or.inl (And.intro (isHexDigit_isAscii h) (Or.inr (Or.inl h)))

theorem all_of_all_of_imp {b : ByteArray} (h : b.data.all p) (imp : ∀ c, p c → q c) : b.data.all q := by
  rw [Array.all_eq] at *
  simp at *
  intro i x
  exact (imp b.data[i]) (h i x)

private theorem autf8EncodeChar_flatMap_ascii {a : List UInt8}
    (is_ascii_list : ∀ (x : UInt8), x ∈ a → x < 128) :
    List.flatMap (fun a => String.utf8EncodeChar (Char.ofUInt8 a)) a = a := by
  have h_encode {i : UInt8} (h : i < 128) : String.utf8EncodeChar (Char.ofUInt8 i) = [i] := by
    simp [Char.ofUInt8, String.utf8EncodeChar, show ¬127 < i.toNat from Nat.not_lt_of_le (Nat.le_pred_of_lt h)]
  induction a with
  | nil => simp
  | cons head tail ih =>
    simp [List.flatMap_cons]
    rw [h_encode]
    · simp
      rw [ih]
      intro x hx
      exact is_ascii_list x (by simp [hx])
    · exact is_ascii_list head (by simp)

private theorem List.toByteArray_loop_eq (xs : List UInt8) (acc : ByteArray) :
    (List.toByteArray.loop xs acc).data = acc.data ++ xs.toArray := by
  induction xs generalizing acc with
  | nil => simp [List.toByteArray.loop]
  | cons x xs ih => simp [List.toByteArray.loop, ih, Array.push]

private theorem ByteArray.toList_toByteArray (ba : ByteArray) :
    ba.data.toList.toByteArray = ba := by
  cases ba with
  | mk data =>
    simp [List.toByteArray]
    apply ByteArray.ext
    simp [List.toByteArray_loop_eq, ByteArray.empty]
    decide

theorem isValidUTF8_of_isAsciiByte (ba : ByteArray) (s : ba.data.all isAsciiByte) : ByteArray.IsValidUTF8 ba := by
  refine ⟨ba.data.toList.map Char.ofUInt8, ?_⟩
  rw [List.utf8Encode]
  simp only [List.flatMap_map]
  have is_ascii : ∀ (x : UInt8), x ∈ ba.data.toList → x < 128 := by
    let is_ascii := Array.all_eq_true_iff_forall_mem.mp s
    simp [isAsciiByte] at is_ascii
    intro x hx
    exact is_ascii x (by simp_all)
  rw [autf8EncodeChar_flatMap_ascii is_ascii]
  exact ByteArray.toList_toByteArray ba |>.symm

/--
A percent-encoded URI component with a compile-time proof that it contains only valid encoded characters.
This provides type-safe URI encoding without runtime validation.

The invariant guarantees that the string contains only unreserved characters (alphanumeric, hyphen, period,
underscore, tilde) and percent signs (for escape sequences).
-/
structure EncodedString (r : UInt8 → Bool) where
  private mk ::

  /--
  The underlying byte array containing the percent-encoded data.
  -/
  toByteArray : ByteArray

  /--
  Proof that all characters in the byte array are valid encoded characters.
  -/
  valid : IsAllowedEncodedChars r toByteArray

namespace EncodedString

/--
Creates an empty encoded string.
-/
def empty : EncodedString r :=
  ⟨.empty, by simp []; exact fun i h => by contradiction⟩

instance : Inhabited (EncodedString r) where
  default := EncodedString.empty

/--
Appends a single encoded character to an encoded string.
Requires that the character is not '%' to maintain the percent-encoding invariant.
-/
private def push (s : EncodedString r) (c : UInt8) (h : isEncodedChar r c) : EncodedString r :=
  ⟨s.toByteArray.push c, IsAllowedEncodedChars.push s.valid h⟩

/--
Converts a byte to its percent-encoded hexadecimal representation (%XX). For example, a space
character (0x20) becomes "%20".
-/
private def byteToHex (b : UInt8) (s : EncodedString r) : EncodedString r :=
  let ba := s.toByteArray.push '%'.toUInt8
    |>.push (hexDigit (b >>> 4))
    |>.push (hexDigit (b &&& 0xF))
  let valid := by
    have h1 : isEncodedChar r '%'.toUInt8 :=
      by simp [isEncodedChar]; decide

    have h2 : isEncodedChar r (hexDigit (b >>> 4)) :=
      let h₀ := hexDigit_isHexDigit (BitVec.toNat_ushiftRight_lt b.toBitVec 4 (by decide))
      isHexDigit_isEncodedChar h₀

    have h3 : isEncodedChar r (hexDigit (b &&& 0xF)) :=
      let h₀ := hexDigit_isHexDigit (@UInt8.and_lt_add_one b 0xF (by decide))
      isHexDigit_isEncodedChar h₀

    exact IsAllowedEncodedChars.push (IsAllowedEncodedChars.push (IsAllowedEncodedChars.push s.valid h1) h2) h3
  ⟨ba, valid⟩

/--
Encodes a raw string into an `EncodedString` with automatic proof construction. Unreserved characters
(alphanumeric, hyphen, period, underscore, tilde) are kept as-is, while all other characters are percent-encoded.
-/
def encode (s : String) : EncodedString r :=
  s.toUTF8.foldl (init := EncodedString.empty) fun acc c =>
    if h : isAsciiByte c ∧ r c then
      acc.push c (by simp [isEncodedChar]; exact And.intro h.left (Or.inl h.right))
    else
      byteToHex c acc

/--
Attempts to create an `EncodedString` from a `ByteArray`. Returns `some` if the byte array contains only
valid encoded characters and all percent signs are followed by exactly two hex digits, `none` otherwise.
-/
def ofByteArray? (ba : ByteArray) : Option (EncodedString r) :=
  if h : IsAllowedEncodedChars r ba then
    if isValidPercentEncoding ba then some ⟨ba, h⟩ else none
  else none

/--
Creates an `EncodedString` from a `ByteArray`, panicking if the byte array is invalid.
-/
def ofByteArray! (ba : ByteArray) : EncodedString r :=
  match ofByteArray? ba with
  | some es => es
  | none => panic! "invalid encoded string"

/--
Creates an `EncodedString` from a `String` by checking if it's already a valid percent-encoded string.
Returns `some` if valid, `none` otherwise.
-/
def ofString? (s : String) : Option (EncodedString r) :=
  ofByteArray? s.toUTF8

/--
Creates an `EncodedString` from a `String`, panicking if the string is not a valid percent-encoded string.
-/
def ofString! (s : String) : EncodedString r :=
  ofByteArray! s.toUTF8

/--
Creates an `EncodedString` from a `ByteArray` with compile-time proofs.
Use this when you have proofs that the byte array is valid.
-/
def new (ba : ByteArray) (valid : IsAllowedEncodedChars r ba) (_validEncoding : isValidPercentEncoding ba) : EncodedString r :=
  ⟨ba, valid⟩

instance : ToString (EncodedString r) where
  toString es := ⟨es.toByteArray, isValidUTF8_of_isAsciiByte es.toByteArray (all_of_all_of_imp es.valid (fun c h => by simp [isEncodedChar] at h; exact h.left))⟩

/--
Decodes an `EncodedString` back to a regular `String`. Converts percent-encoded sequences (e.g., "%20")
back to their original characters. Returns `none` if the decoded bytes are not valid UTF-8.
-/
def decode (es : EncodedString r) : Option String := Id.run do
  let mut decoded : ByteArray := ByteArray.empty
  let rawBytes := es.toByteArray
  let len := rawBytes.size
  let mut i := 0
  let percent := '%'.toNat.toUInt8
  while h : i < len do
    let c := rawBytes[i]
    (decoded, i) := if h₁ : c == percent ∧ i + 1 < len then
      let h1 := rawBytes[i + 1]
      if let some hd1 := hexDigitToUInt8? h1 then
        if h₂ : i + 2 < len then
          let h2 := rawBytes[i + 2]
          if let some hd2 := hexDigitToUInt8? h2 then
            (decoded.push (hd1 * 16 + hd2), i + 3)
          else
            (((decoded.push c).push h1).push h2, i + 3)
        else
          ((decoded.push c).push h1, i + 2)
      else
        ((decoded.push c).push h1, i + 2)
    else
      (decoded.push c, i + 1)
  return String.fromUTF8? decoded

instance : Repr (EncodedString r) where
  reprPrec es n := reprPrec (toString es) n

instance : BEq (EncodedString r) where
  beq x y := x.toByteArray = y.toByteArray

instance : Hashable (EncodedString r) where
  hash x := Hashable.hash x.toByteArray

end EncodedString

/--
A percent-encoded query string component with a compile-time proof that it contains only valid encoded
query characters. Extends `EncodedString` to admit '+', which a query may carry literally as a
sub-delim.

A '+' stands for itself, as RFC 3986 defines it, and not for a space the way
application/x-www-form-urlencoded reads it. A space is written "%20".

Reference: https://www.rfc-editor.org/rfc/rfc3986.html#section-3.4
-/
structure EncodedQueryString (r : UInt8 → Bool) where
  private mk ::

  /--
  The underlying byte array containing the percent-encoded query data.
  -/
  toByteArray : ByteArray

  /--
  Proof that all characters in the byte array are valid encoded query characters.
  -/
  valid : IsAllowedEncodedQueryChars r toByteArray

namespace EncodedQueryString

/--
Creates an empty encoded query string.
-/
def empty : EncodedQueryString r :=
  ⟨.empty, by simp; intro a h; contradiction⟩

instance : Inhabited (EncodedQueryString r) where
  default := EncodedQueryString.empty

/--
Checks whether an encoded query string carries no bytes at all.
-/
def isEmpty (s : EncodedQueryString r) : Bool :=
  s.toByteArray.isEmpty

/--
Appends a single encoded query character to an encoded query string.
-/
private def push (s : EncodedQueryString r) (c : UInt8) (h : isEncodedQueryChar r c) : EncodedQueryString r :=
  ⟨s.toByteArray.push c, IsAllowedEncodedQueryChars.push s.valid h⟩

/--
Attempts to create an `EncodedQueryString` from a `ByteArray`. Returns `some` if the byte array contains
only valid encoded query characters and all percent signs are followed by exactly two hex digits, `none` otherwise.
-/
def ofByteArray? (ba : ByteArray) (r : UInt8 → Bool := isQueryChar) : Option (EncodedQueryString r) :=
  if h : IsAllowedEncodedQueryChars r ba then
    if isValidPercentEncoding ba then some ⟨ba, h⟩ else none
  else none

/--
Creates an `EncodedQueryString` from a `ByteArray`, panicking if the byte array is invalid.
-/
def ofByteArray! (ba : ByteArray) (r : UInt8 → Bool := isQueryChar) : EncodedQueryString r :=
  match ofByteArray? ba r with
  | some es => es
  | none => panic! "invalid encoded query string"

/--
Creates an `EncodedQueryString` from a `String` by checking if it's already a valid percent-encoded string.
Returns `some` if valid, `none` otherwise.
-/
def ofString? (s : String) (r : UInt8 → Bool := isQueryChar) : Option (EncodedQueryString r) :=
  ofByteArray? s.toUTF8 r

/--
Creates an `EncodedQueryString` from a `String`, panicking if the string is not a valid percent-encoded string.
-/
def ofString! (s : String) (r : UInt8 → Bool := isQueryChar) : EncodedQueryString r :=
  ofByteArray! s.toUTF8 r

/--
Creates an `EncodedQueryString` from a `ByteArray` with compile-time proofs.
Use this when you have proofs that the byte array is valid.
-/
def new (ba : ByteArray) (valid : IsAllowedEncodedQueryChars r ba) (_validEncoding : isValidPercentEncoding ba) : EncodedQueryString r :=
  ⟨ba, valid⟩

/--
Converts a byte to its percent-encoded hexadecimal representation (%XX). For example, a space character
(0x20) becomes "%20".
-/
private def byteToHex (b : UInt8) (s : EncodedQueryString r) : EncodedQueryString r :=
  let ba := s.toByteArray.push '%'.toUInt8
    |>.push (hexDigit (b >>> 4))
    |>.push (hexDigit (b &&& 0xF))
  let valid := by
    have h1 : isEncodedQueryChar r '%'.toUInt8 := by
      simp [isEncodedQueryChar, isEncodedChar]; decide
    have h2 : isEncodedQueryChar r (hexDigit (b >>> 4)) :=
      isHexDigit_isEncodedQueryChar (hexDigit_isHexDigit (BitVec.toNat_ushiftRight_lt b.toBitVec 4 (by decide)))
    have h3 : isEncodedQueryChar r (hexDigit (b &&& 0xF)) :=
      isHexDigit_isEncodedQueryChar (hexDigit_isHexDigit (@UInt8.and_lt_add_one b 0xF (by decide)))
    exact IsAllowedEncodedQueryChars.push (IsAllowedEncodedQueryChars.push (IsAllowedEncodedQueryChars.push s.valid h1) h2) h3
  ⟨ba, valid⟩

/--
Appends raw bytes, percent-encoding every byte the rule `rd` does not admit. `rd` may be stricter
than the string's own rule `r`, which is how a name or a value gets the separators escaped inside a
query that is allowed to carry them literally.
-/
private def encodeBytesInto (acc : EncodedQueryString r) (bs : ByteArray) (rd : UInt8 → Bool)
    (hrd : ∀ c, rd c = true → r c = true) : EncodedQueryString r :=
  bs.foldl (init := acc) fun acc c =>
    if h : isAsciiByte c ∧ rd c then
      acc.push c (by
        simp [isEncodedQueryChar, isEncodedChar]
        exact Or.inl (And.intro h.left (Or.inl (hrd c h.right))))
    else
      byteToHex c acc

/--
Encodes raw bytes into an `EncodedQueryString` with automatic proof construction. Bytes allowed by `r`
are kept as-is and all others are percent-encoded, so a space becomes "%20".

Every byte has exactly one spelling here, so for a rule that admits no character which may also appear
percent-encoded, such as `isUnreserved`, the result is the canonical spelling of those bytes.
-/
def encodeBytes (bs : ByteArray) (r : UInt8 → Bool := isQueryChar) : EncodedQueryString r :=
  encodeBytesInto EncodedQueryString.empty bs r (fun _ h => h)

/--
Encodes a raw string into an `EncodedQueryString` with automatic proof construction. Characters allowed
by `r` are kept as-is and all others are percent-encoded, so a space becomes "%20".
-/
def encode (s : String) (r : UInt8 → Bool := isQueryChar) : EncodedQueryString r :=
  encodeBytes s.toUTF8 r

/--
Converts an `EncodedQueryString` to a `String`, given a proof that all characters satisfying `r` are ASCII.
-/
def toString (es : EncodedQueryString r) : String :=
  ⟨es.toByteArray, isValidUTF8_of_isAsciiByte es.toByteArray (all_of_all_of_imp es.valid (fun c h => isEncodedQueryChar_isAscii c h))⟩

/--
Resolves the percent-encoded sequences in a validated query component. With `plusIsSpace`, a '+' is
also read as a space, which is how application/x-www-form-urlencoded spells one; otherwise it is an
ordinary sub-delim standing for itself, as RFC 3986 has it.

This is almost the same code from `System.Uri.UriEscape.decodeUri`.
-/
private def decodeRaw (rawBytes : ByteArray) (plusIsSpace : Bool) : ByteArray := Id.run do
  let mut decoded : ByteArray := ByteArray.empty
  let len := rawBytes.size
  let mut i := 0
  let percent := '%'.toNat.toUInt8
  let plus := '+'.toNat.toUInt8
  while h : i < len do
    let c := rawBytes[i]
    (decoded, i) := if plusIsSpace ∧ c == plus then
      (decoded.push ' '.toNat.toUInt8, i + 1)
    else if h₁ : c == percent ∧ i + 1 < len then
      let h1 := rawBytes[i + 1]
      if let some hd1 := hexDigitToUInt8? h1 then
        if h₂ : i + 2 < len then
          let h2 := rawBytes[i + 2]
          if let some hd2 := hexDigitToUInt8? h2 then
            (decoded.push (hd1 * 16 + hd2), i + 3)
          else
            (((decoded.push c).push h1).push h2, i + 3)
        else
          ((decoded.push c).push h1, i + 2)
      else
        ((decoded.push c).push h1, i + 2)
    else
      (decoded.push c, i + 1)
  return decoded

/--
Decodes an `EncodedQueryString` back to the bytes it stands for, by resolving its percent-encoded
sequences. A '+' is an ordinary sub-delim here and stands for itself, not for a space.
-/
def decodeBytes (es : EncodedQueryString r) : ByteArray :=
  decodeRaw es.toByteArray (plusIsSpace := false)

/--
Decodes an `EncodedQueryString` back to a regular `String` by resolving its percent-encoded sequences.
Returns `none` if the decoded bytes are not valid UTF-8.
-/
def decode (es : EncodedQueryString r) : Option String :=
  String.fromUTF8? es.decodeBytes

end EncodedQueryString

instance : ToString (EncodedQueryString r) where
  toString := EncodedQueryString.toString

instance : Repr (EncodedQueryString r) where
  reprPrec es n := reprPrec (toString es) n

instance : BEq (EncodedQueryString r) where
  beq x y := x.toByteArray = y.toByteArray

instance : Hashable (EncodedQueryString r) where
  hash x := Hashable.hash x.toByteArray

instance : Hashable (Option (EncodedQueryString r)) where
  hash
    | some x =>  Hashable.hash ((ByteArray.mk #[1] ++ x.toByteArray))
    | none =>  Hashable.hash (ByteArray.mk #[0])

/--
A percent-encoded URI path segment. Valid characters are `pchar` (unreserved, sub-delims, ':', '@').
-/
abbrev EncodedSegment := EncodedString isPChar

namespace EncodedSegment

/--
Encodes a raw string into an encoded path segment.
-/
def encode (s : String) : EncodedSegment :=
  EncodedString.encode (r := isPChar) s

/--
Attempts to create an encoded path segment from raw bytes.
-/
def ofByteArray? (ba : ByteArray) : Option EncodedSegment :=
  EncodedString.ofByteArray? (r := isPChar) ba

/--
Creates an encoded path segment from raw bytes, panicking on invalid encoding.
-/
def ofByteArray! (ba : ByteArray) : EncodedSegment :=
  EncodedString.ofByteArray! (r := isPChar) ba

/--
Decodes an encoded path segment back to a UTF-8 string.
-/
def decode (segment : EncodedSegment) : Option String :=
  EncodedString.decode segment

end EncodedSegment

/--
A percent-encoded URI fragment component. Valid characters are `pchar / "/" / "?"`.
-/
abbrev EncodedFragment := EncodedString isFragmentChar

namespace EncodedFragment

/--
Encodes a raw string into an encoded fragment component.
-/
def encode (s : String) : EncodedFragment :=
  EncodedString.encode (r := isFragmentChar) s

/--
Attempts to create an encoded fragment component from raw bytes.
-/
def ofByteArray? (ba : ByteArray) : Option EncodedFragment :=
  EncodedString.ofByteArray? (r := isFragmentChar) ba

/--
Creates an encoded fragment component from raw bytes, panicking on invalid encoding.
-/
def ofByteArray! (ba : ByteArray) : EncodedFragment :=
  EncodedString.ofByteArray! (r := isFragmentChar) ba

/--
Decodes an encoded fragment component back to a UTF-8 string.
-/
def decode (fragment : EncodedFragment) : Option String :=
  EncodedString.decode fragment

end EncodedFragment

/--
A percent-encoded URI userinfo component. Valid characters are `unreserved / sub-delims / ":"`.
-/
abbrev EncodedUserInfo := EncodedString isUserInfoChar

namespace EncodedUserInfo

/--
Encodes a raw string into an encoded userinfo component.
-/
def encode (s : String) : EncodedUserInfo :=
  EncodedString.encode (r := isUserInfoChar) s

/--
Attempts to create an encoded userinfo component from raw bytes.
-/
def ofByteArray? (ba : ByteArray) : Option EncodedUserInfo :=
  EncodedString.ofByteArray? (r := isUserInfoChar) ba

/--
Creates an encoded userinfo component from raw bytes, panicking on invalid encoding.
-/
def ofByteArray! (ba : ByteArray) : EncodedUserInfo :=
  EncodedString.ofByteArray! (r := isUserInfoChar) ba

/--
Decodes an encoded userinfo component back to a UTF-8 string.
-/
def decode (userInfo : EncodedUserInfo) : Option String :=
  EncodedString.decode userInfo

end EncodedUserInfo

/--
A percent-encoded URI query parameter. Valid characters are `pchar / "/" / "?"` minus the '&' and '='
separators, which must be percent-encoded to appear in a name or a value.
-/
abbrev EncodedQueryParam := EncodedQueryString isQueryDataChar

namespace EncodedQueryParam

/--
Encodes a raw string into an encoded query parameter.
-/
def encode (s : String) : EncodedQueryParam :=
  EncodedQueryString.encode (r := isQueryDataChar) s

/--
Attempts to create an encoded query parameter from raw bytes.
-/
def ofByteArray? (ba : ByteArray) : Option EncodedQueryParam :=
  EncodedQueryString.ofByteArray? (r := isQueryDataChar) ba

/--
Creates an encoded query parameter from raw bytes, panicking on invalid encoding.
-/
def ofByteArray! (ba : ByteArray) : EncodedQueryParam :=
  EncodedQueryString.ofByteArray! (r := isQueryDataChar) ba

/--
Attempts to create an encoded query parameter from an encoded string.
-/
def fromString? (s : String) : Option EncodedQueryParam :=
  EncodedQueryString.ofString? (r := isQueryDataChar) s

/--
Decodes an encoded query parameter back to a UTF-8 string.
-/
def decode (param : EncodedQueryParam) : Option String :=
  EncodedQueryString.decode param

end EncodedQueryParam

/--
The name or the value of a query parameter, as the bytes it stands for rather than as one of its
spellings. Percent-encoding is not canonical, so `a%3Ab` and `a:b` are two spellings of the same
parameter; a `QueryParam` is that parameter.

A '+' is a sub-delim rather than a space, so `a+b` and `a%20b` are different parameters.

Reference: https://www.rfc-editor.org/rfc/rfc3986.html#section-3.4
-/
structure QueryParam where
  /--
  The bytes this parameter stands for. They are not percent-encoded and need not be valid UTF-8,
  since a percent-encoded sequence may denote any byte.
  -/
  toByteArray : ByteArray
deriving Inhabited

namespace QueryParam

/--
The parameter named by a string.
-/
def ofString (s : String) : QueryParam :=
  ⟨s.toUTF8⟩

/--
The parameter's name as a string, or `none` if its bytes are not valid UTF-8.
-/
def toString? (param : QueryParam) : Option String :=
  String.fromUTF8? param.toByteArray

/--
The spelling this parameter takes on the wire, with everything a query may not carry literally,
such as a space or a separator, percent-encoded.
-/
def encode (param : QueryParam) : EncodedQueryParam :=
  EncodedQueryString.encodeBytes param.toByteArray isQueryDataChar

instance : BEq QueryParam where
  beq x y := x.toByteArray == y.toByteArray

instance : Hashable QueryParam where
  hash x := Hashable.hash x.toByteArray

-- A parameter's bytes need not be valid UTF-8, so it is shown as the spelling it takes on the wire.
instance : Repr QueryParam where
  reprPrec param n := reprPrec (EncodedQueryString.toString param.encode) n

end QueryParam

namespace EncodedQueryParam

/--
The parameter this spelling stands for.
-/
def toQueryParam (param : EncodedQueryParam) : QueryParam :=
  ⟨param.decodeBytes⟩

end EncodedQueryParam

/--
A percent-encoded URI query component, the whole of what follows a '?'. RFC 3986 leaves its contents
opaque: valid characters are `pchar / "/" / "?"`, and nothing in the grammar gives '&' or '=' any
meaning. Reading it as parameters is a separate convention, applied by `params`, which a consumer
that gives the query a meaning of its own can ignore.

Those parameters are read on the first lookup and kept afterwards, so a component nobody inspects is
never split, and one that is inspected repeatedly is split once.

Reference: https://www.rfc-editor.org/rfc/rfc3986.html#section-3.4
-/
structure EncodedQuery where
  private mk ::

  /--
  The component as it was written, percent-encoding and all.
  -/
  encoded : EncodedQueryString isQueryChar

  /--
  The parameters `encoded` spells out, read on first use.
  -/
  private parameters : Thunk (Array (QueryParam × Option QueryParam))

namespace EncodedQuery

/--
Reads a validated query component as '&'-separated `name=value` pairs.

This is the form convention rather than anything RFC 3986 defines, so it never fails: the first '='
in a pair separates the name from the value, leaving a value free to contain further '=' as base64
padding does, a pair with no '=' is a name with no value, and an empty pair contributes nothing.
-/
private def paramsOf (bytes : ByteArray) (plusIsSpace : Bool) : Array (QueryParam × Option QueryParam) := Id.run do
  let ampersand := '&'.toUInt8
  let equals := '='.toUInt8

  let mut params := #[]
  let mut start := 0
  let mut separator := none
  let mut i := 0

  let pair := fun (start stop : Nat) (separator : Option Nat) =>
    let decode := fun (start stop : Nat) =>
      QueryParam.mk (EncodedQueryString.decodeRaw (bytes.extract start stop) plusIsSpace)
    match separator with
    | none => (decode start stop, none)
    | some separator => (decode start separator, some (decode (separator + 1) stop))

  while h : i < bytes.size do
    let c := bytes[i]
    if c == ampersand then
      if start < i then
        params := params.push (pair start i separator)
      start := i + 1
      separator := none
    else if c == equals && separator.isNone then
      separator := some i
    i := i + 1

  if start < bytes.size then
    params := params.push (pair start bytes.size separator)

  return params

private def ofEncoded (encoded : EncodedQueryString isQueryChar) : EncodedQuery :=
  EncodedQuery.mk encoded (Thunk.mk fun _ => paramsOf encoded.toByteArray (plusIsSpace := false))

/--
The parameters this query spells out, with '+' standing for itself as RFC 3986 defines it.
-/
def params (query : EncodedQuery) : Array (QueryParam × Option QueryParam) :=
  query.parameters.get

/--
The parameters this component spells out when it is an application/x-www-form-urlencoded payload,
where a '+' stands for a space. Use this for a submitted form body, not for the query of a URI.

Unlike `params`, this reading is not kept, since a body is normally read once.
-/
def formParams (query : EncodedQuery) : Array (QueryParam × Option QueryParam) :=
  paramsOf query.encoded.toByteArray (plusIsSpace := true)

/--
The component's underlying bytes.
-/
def toByteArray (query : EncodedQuery) : ByteArray :=
  query.encoded.toByteArray

/--
Checks whether the component carries no bytes at all, as in a URI ending in a bare '?'.
-/
def isEmpty (query : EncodedQuery) : Bool :=
  query.encoded.isEmpty

/--
The empty query component, as in a URI ending in a bare '?'.
-/
def empty : EncodedQuery :=
  ofEncoded EncodedQueryString.empty

/--
Encodes a raw string into an encoded query component.
-/
def encode (s : String) : EncodedQuery :=
  ofEncoded (EncodedQueryString.encode (r := isQueryChar) s)

/--
Attempts to create an encoded query component from raw bytes.
-/
def ofByteArray? (ba : ByteArray) : Option EncodedQuery :=
  (EncodedQueryString.ofByteArray? (r := isQueryChar) ba).map ofEncoded

/--
Creates an encoded query component from raw bytes, panicking on invalid encoding.
-/
def ofByteArray! (ba : ByteArray) : EncodedQuery :=
  ofEncoded (EncodedQueryString.ofByteArray! (r := isQueryChar) ba)

/--
Attempts to create an encoded query component from an encoded string.
-/
def fromString? (s : String) : Option EncodedQuery :=
  (EncodedQueryString.ofString? (r := isQueryChar) s).map ofEncoded

/--
Decodes an encoded query component back to a UTF-8 string. This resolves the percent-encoded
sequences across the whole component, including any '&' and '=' it uses as separators, so the result
is no longer a query that can be split into parameters.
-/
def decode (query : EncodedQuery) : Option String :=
  EncodedQueryString.decode query.encoded

private theorem isQueryChar_of_isQueryDataChar (c : UInt8) (h : isQueryDataChar c = true) :
    isQueryChar c = true := by
  simp [isQueryDataChar, Bool.and_eq_true] at h
  exact h.left.left

private def appendParam (acc : EncodedQueryString isQueryChar) (param : QueryParam) : EncodedQueryString isQueryChar :=
  EncodedQueryString.encodeBytesInto acc param.toByteArray isQueryDataChar isQueryChar_of_isQueryDataChar

private def appendByte (acc : EncodedQueryString isQueryChar) (c : UInt8)
    (h : isEncodedQueryChar isQueryChar c) : EncodedQueryString isQueryChar :=
  EncodedQueryString.push acc c h

private def appendPair (acc : EncodedQueryString isQueryChar) (key : QueryParam)
    (value : Option QueryParam) : EncodedQueryString isQueryChar :=
  let acc := if acc.isEmpty then acc else appendByte acc '&'.toUInt8 (by decide)
  let acc := appendParam acc key
  match value with
  | none => acc
  | some value => appendParam (appendByte acc '='.toUInt8 (by decide)) value

/--
Appends a parameter to a query component, leaving the parameters already spelled out there untouched.
Everything the name or the value may not carry literally, including the '&' and '=' separators, is
percent-encoded, so the result splits back into the previous parameters followed by this one.
-/
def insert (query : EncodedQuery) (key : QueryParam) (value : Option QueryParam) : EncodedQuery :=
  ofEncoded (appendPair query.encoded key value)

/--
The query component that spells out these parameters.
-/
def ofParams (params : Array (QueryParam × Option QueryParam)) : EncodedQuery :=
  ofEncoded <| params.foldl (init := EncodedQueryString.empty) fun acc (key, value) =>
    appendPair acc key value

end EncodedQuery

instance : Inhabited EncodedQuery := ⟨EncodedQuery.empty⟩

instance : ToString EncodedQuery where
  toString query := toString query.encoded

instance : Repr EncodedQuery where
  reprPrec query n := reprPrec (toString query.encoded) n

instance : BEq EncodedQuery where
  beq x y := x.encoded == y.encoded

end Std.Http.URI
