/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.System.Uri
public import Init.Data.String

public section

namespace Std.Http.URI

set_option linter.all true

/-!
# URI Encoding

This module provides utilities for percent-encoding URI components according to RFC 3986. It includes
character validation, encoding/decoding functions, and types that maintain encoding invariants through
Lean's dependent type system.
-/

/--
Checks if a byte represents an ASCII character (value < 128).
-/
def isAscii (c : UInt8) : Bool :=
  c < 128

/--
Checks if all bytes in a `ByteArray` are ASCII characters.
-/
abbrev isAsciiByteArray (c : ByteArray) : Bool :=
  c.data.all isAscii

instance : Decidable (isAsciiByteArray s) :=
  inferInstanceAs (Decidable (s.data.all isAscii = true))

/--
Checks if a byte is a hexadecimal digit (0-9, a-f, or A-F). Note: This accepts both lowercase and
uppercase hex digits.
-/
def isHexDigit (c : UInt8) : Bool :=
  (c ≥ '0'.toUInt8 && c ≤ '9'.toUInt8) ||
  (c ≥ 'a'.toUInt8 && c ≤ 'z'.toUInt8) ||
  (c ≥ 'A'.toUInt8 && c ≤ 'Z'.toUInt8)

/--
Checks if a byte is an unreserved character according to RFC 3986. Unreserved characters are:
alphanumeric, hyphen, period, underscore, and tilde.
-/
def isUnreserved (c : UInt8) : Bool :=
  isHexDigit c ||
  (c = '-'.toUInt8 || c = '.'.toUInt8 || c = '_'.toUInt8 || c = '~'.toUInt8)

/--
Checks if a byte is allowed in a URI path component (RFC 3986 pchar). Includes unreserved characters
plus common sub-delimiters and gen-delimiters used in paths.
-/
def isPathAllowed (c : UInt8) : Bool :=
  isUnreserved c
  || c = ':'.toUInt8 || c = '@'.toUInt8 || c = '!'.toUInt8 || c = '$'.toUInt8
  || c = '&'.toUInt8 || c = '\''.toUInt8 || c = '('.toUInt8 || c = ')'.toUInt8
  || c = '*'.toUInt8 || c = '+'.toUInt8 || c = ','.toUInt8 || c = ';'.toUInt8
  || c = '='.toUInt8

/--
Checks if a byte is a valid character in a percent-encoded URI component. Valid characters are
unreserved characters or the percent sign (for escape sequences).
-/
def isEncodedChar (c : UInt8) : Bool :=
  isUnreserved c || c = '%'.toUInt8

/--
Checks if a byte is valid in a percent-encoded query string component. Extends `isEncodedChar` to also
allow '+' which represents space in application/x-www-form-urlencoded format.
-/
def isEncodedQueryChar (c : UInt8) : Bool :=
  isEncodedChar c || c = '+'.toUInt8

/--
Checks if all characters in a `ByteArray` are allowed in an encoded URI component. This is a fast check
that only verifies the character set, not full encoding validity.
-/
@[inline]
abbrev isAllowedEncodedChars (s : ByteArray) : Prop :=
  s.data.all isEncodedChar

instance : Decidable (isAllowedEncodedChars s) :=
  inferInstanceAs (Decidable (s.data.all isEncodedChar = true))

/--
Checks if all characters in a `ByteArray` are allowed in an encoded query parameter. Allows '+' as an
alternative encoding for space (application/x-www-form-urlencoded).
-/
@[inline]
abbrev isAllowedEncodedQueryChars (s : ByteArray) : Prop :=
  s.data.all isEncodedQueryChar

instance : Decidable (isAllowedEncodedQueryChars s) :=
  inferInstanceAs (Decidable (s.data.all isEncodedQueryChar = true))

/--
Converts a nibble (4-bit value, 0-15) to its hexadecimal digit representation. Returns '0'-'9' for
values 0-9, and 'A'-'F' for values 10-15.
-/
def hexDigit (n : UInt8) : UInt8 :=
  if n < 10 then (n + '0'.toUInt8)
  else (n - 10 + 'A'.toUInt8)

theorem isAsciiByteArray.push {bs : ByteArray} (h : isAsciiByteArray bs) (h₁ : isAscii c) :
    isAsciiByteArray (bs.push c) := by
  simpa [isAsciiByteArray, ByteArray.push, Array.all_push, And.intro h h₁]

theorem isAllowedEncodedChars.push {bs : ByteArray} (h : isAllowedEncodedChars bs) (h₁ : isEncodedChar c) :
    isAllowedEncodedChars (bs.push c) := by
  simpa [isAllowedEncodedChars, ByteArray.push, Array.all_push, And.intro h h₁]

theorem isAllowedEncodedQueryChars.push {bs : ByteArray} (h : isAllowedEncodedQueryChars bs) (h₁ : isEncodedQueryChar c) :
    isAllowedEncodedQueryChars (bs.push c) := by
  simpa [isAllowedEncodedQueryChars, ByteArray.push, Array.all_push, And.intro h h₁]

theorem add_sub_assoc {w : Nat} {n m k : BitVec w} :
    n + (m - k) = n - k + m := by
  rw [BitVec.sub_eq_add_neg, BitVec.add_comm m, ← BitVec.add_assoc, ← BitVec.sub_eq_add_neg]

theorem isHexDigit_isAscii {c : UInt8} (h : isHexDigit c) : isAscii c := by
  unfold isHexDigit isAscii at *
  simp at h
  rcases h with ⟨h1, h2⟩
  next => simp; exact Nat.lt_of_le_of_lt h2 (by decide)
  next h => simp; exact Nat.lt_of_le_of_lt h.2 (by decide)
  next h => simp; exact Nat.lt_of_le_of_lt h.2 (by decide)

theorem isEncodedChar_isAscii (c : UInt8) (h : isEncodedChar c) : isAscii c := by
  unfold isEncodedChar isUnreserved at *
  cases h' : isHexDigit c
  · simp [h'] at *; rcases h with ⟨h, h⟩ | h | h | h <;> (subst_vars; decide)
  · simp [h'] at h; exact (isHexDigit_isAscii h')

theorem isEncodedQueryChar_isAscii (c : UInt8) (h : isEncodedQueryChar c) : isAscii c := by
  unfold isEncodedQueryChar isAscii at *
  simp at h
  rcases h
  next h => exact isEncodedChar_isAscii c h
  next h => subst_vars; decide

theorem hexDigit_isHexDigit (h₀ : x < 16) : isHexDigit (hexDigit x) := by
  unfold hexDigit isHexDigit
  have h₁ : x.toNat < 16 := h₀
  split <;> simp [Char.toUInt8]

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
    have h₅ : x.toNat - 10 + 65 ≤ 90 := by omega
    have h₄ : x.toNat - 10 + 65 < 256 := by omega

    refine Or.inr ⟨?_, ?_⟩
    · simpa [UInt8.ofNat_sub (by omega : 10 ≤ x.toNat)] using
        UInt8.ofNat_le_iff_le (by decide : 65 < 256) h₄ |>.mpr h₃
    · simpa [UInt8.ofNat_add, UInt8.ofNat_sub (by omega : 10 ≤ x.toNat)] using
        UInt8.ofNat_le_iff_le h₄ (by decide : 90 < 256) |>.mpr h₅

theorem isHexDigit_isEncodedChar {c : UInt8} (h : isHexDigit c) : isEncodedChar c := by
  unfold isEncodedChar isUnreserved
  simp at *
  exact Or.inl (Or.inl h)

theorem isHexDigit_isEncodedQueryChar {c : UInt8} (h : isHexDigit c) : isEncodedQueryChar c := by
  unfold isEncodedQueryChar isEncodedChar isUnreserved
  simp at *
  exact Or.inl (Or.inl (Or.inl h))

theorem all_of_all_of_imp {b : ByteArray} (h : b.data.all p) (imp : ∀ c, p c → q c) : b.data.all q := by
  rw [Array.all_eq] at *
  simp at *
  intro i x
  exact (imp b.data[i]) (h i x)

theorem autf8EncodeChar_flatMap_ascii {a : List UInt8}
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

theorem List.toByteArray_loop_eq (xs : List UInt8) (acc : ByteArray) :
    (List.toByteArray.loop xs acc).data = acc.data ++ xs.toArray := by
  induction xs generalizing acc with
  | nil => simp [List.toByteArray.loop]
  | cons x xs ih => simp [List.toByteArray.loop, ih, Array.push]

theorem ByteArray.toList_toByteArray (ba : ByteArray) :
    ba.data.toList.toByteArray = ba := by
  cases ba with
  | mk data =>
    simp [List.toByteArray]
    apply ByteArray.ext
    simp [List.toByteArray_loop_eq, ByteArray.empty]
    decide

theorem ascii_is_valid_utf8 (ba : ByteArray) (s : ba.data.all isAscii) : ByteArray.IsValidUTF8 ba := by
  refine ⟨ba.data.toList.map Char.ofUInt8, ?_⟩
  rw [List.utf8Encode]
  simp only [List.flatMap_map]
  have is_ascii : ∀ (x : UInt8), x ∈ ba.data.toList → x < 128 := by
    let is_ascii := Array.all_eq_true_iff_forall_mem.mp s
    simp [isAscii] at is_ascii
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
structure EncodedString where
  mk ::

  /-- The underlying byte array containing the percent-encoded data. -/
  toByteArray : ByteArray

  /-- Proof that all characters in the byte array are valid encoded characters. -/
  valid : isAllowedEncodedChars toByteArray

namespace EncodedString

/-- Creates an empty encoded string. -/
def empty : EncodedString :=
  ⟨.empty, by native_decide⟩

/-- Appends a single encoded character to an encoded string. -/
def push (s : EncodedString) (c : UInt8) (h : isEncodedChar c) : EncodedString where
  toByteArray := s.toByteArray.push c
  valid := isAllowedEncodedChars.push s.valid h

/--
Converts a byte to its percent-encoded hexadecimal representation (%XX). For example, a space
character (0x20) becomes "%20".
-/
def byteToHex (b : UInt8) (s : EncodedString) : EncodedString :=
  s.push '%'.toUInt8 (by decide)
    |>.push (hexDigit (b >>> 4)) (isHexDigit_isEncodedChar (hexDigit_isHexDigit (BitVec.toNat_ushiftRight_lt b.toBitVec 4 (by decide))))
    |>.push (hexDigit (b &&& 0xF)) (isHexDigit_isEncodedChar (hexDigit_isHexDigit (@UInt8.and_lt_add_one b 0xF (by decide))))

/--
Encodes a raw string into an `EncodedString` with automatic proof construction. Unreserved characters
(alphanumeric, hyphen, period, underscore, tilde) are kept as-is, while all other characters are percent-encoded.
-/
def encode (s : String) : EncodedString :=
  s.toUTF8.foldl (init := EncodedString.empty) fun acc c =>
    if h : isUnreserved c then
      acc.push c (by simp [isEncodedChar]; exact Or.inl h)
    else
      byteToHex c acc

/--
Attempts to create an `EncodedString` from a `ByteArray`. Returns `some` if the byte array contains only
valid encoded characters, `none` otherwise.
-/
def fromByteArray? (ba : ByteArray) : Option EncodedString :=
  if h : isAllowedEncodedChars ba then some ⟨ba, h⟩  else none

instance : ToString EncodedString where
  toString es := ⟨es.toByteArray, ascii_is_valid_utf8 es.toByteArray (all_of_all_of_imp es.valid isEncodedChar_isAscii)⟩

/--
Decodes an `EncodedString` back to a regular `String`. Converts percent-encoded sequences (e.g., "%20")
back to their original characters.
-/
def decode (es : EncodedString) : String :=
  System.Uri.UriEscape.decodeUri (toString es)

instance : Repr EncodedString where
  reprPrec es := reprPrec (toString es)

instance : Inhabited EncodedString where
  default := EncodedString.empty

instance : BEq EncodedString where
  beq x y := x.toByteArray = y.toByteArray

instance : Hashable EncodedString where
  hash x := Hashable.hash x.toByteArray

end EncodedString

/--
A percent-encoded query string component with a compile-time proof that it contains only valid encoded
query characters. Extends `EncodedString` to support the '+' character for spaces, following the
application/x-www-form-urlencoded format.

This type is specifically designed for encoding query parameters where spaces can be represented as '+'
instead of "%20".
-/
structure EncodedQueryString where
  mk ::

  /-- The underlying byte array containing the percent-encoded query data. -/
  toByteArray : ByteArray

  /-- Proof that all characters in the byte array are valid encoded query characters. -/
  valid : isAllowedEncodedQueryChars toByteArray

namespace EncodedQueryString

/-- Creates an empty encoded query string. -/
def empty : EncodedQueryString :=
  ⟨.empty, by native_decide⟩

/-- Appends a single encoded query character to an encoded query string. -/
def push (s : EncodedQueryString) (c : UInt8) (h : isEncodedQueryChar c) : EncodedQueryString where
  toByteArray := s.toByteArray.push c
  valid := isAllowedEncodedQueryChars.push s.valid h

/--
Attempts to create an `EncodedQueryString` from a `ByteArray`. Returns `some` if the byte array contains
only valid encoded query characters, `none` otherwise.
-/
def fromByteArray? (ba : ByteArray) : Option EncodedQueryString :=
  if h : isAllowedEncodedQueryChars ba then some ⟨ba, h⟩  else none

/--
Converts a byte to its percent-encoded hexadecimal representation (%XX). For example, a space character
(0x20) becomes "%20".
-/
def byteToHex (b : UInt8) (s : EncodedQueryString) : EncodedQueryString :=
  s.push '%'.toUInt8 (by decide)
    |>.push (hexDigit (b >>> 4)) (isHexDigit_isEncodedQueryChar (hexDigit_isHexDigit (BitVec.toNat_ushiftRight_lt b.toBitVec 4 (by decide))))
    |>.push (hexDigit (b &&& 0xF)) (isHexDigit_isEncodedQueryChar (hexDigit_isHexDigit (@UInt8.and_lt_add_one b 0xF (by decide))))

/--
Encodes a raw string into an `EncodedQueryString` with automatic proof construction. Unreserved characters
are kept as-is, spaces are encoded as '+', and all other characters are percent-encoded.
-/
def encode (s : String) : EncodedQueryString :=
  s.toUTF8.foldl (init := EncodedQueryString.empty) fun acc c =>
    if h : isUnreserved c then
      acc.push c (by simp [isEncodedQueryChar, isEncodedChar]; exact Or.inl (Or.inl h))
    else if h : c = ' '.toUInt8 then
      acc.push '+'.toUInt8 (by simp [isEncodedQueryChar])
    else
      byteToHex c acc

instance : ToString EncodedQueryString where
  toString es := ⟨es.toByteArray, ascii_is_valid_utf8 es.toByteArray (all_of_all_of_imp es.valid isEncodedQueryChar_isAscii)⟩

/--
Decodes an `EncodedQueryString` back to a regular `String`. Converts percent-encoded sequences and '+'
signs back to their original characters.
-/
def decode (es : EncodedQueryString) : String :=
  System.Uri.UriEscape.decodeUri (toString es |>.replace "+" "%20")

end EncodedQueryString

instance : Repr EncodedQueryString where
  reprPrec es := reprPrec (toString es)

instance : Inhabited EncodedQueryString where
  default := EncodedQueryString.empty

instance : BEq EncodedQueryString where
  beq x y := x.toByteArray = y.toByteArray

instance : Hashable EncodedQueryString where
  hash x := Hashable.hash x.toByteArray

instance : Hashable (Option EncodedQueryString) where
  hash
    | some x =>  Hashable.hash ((ByteArray.mk #[1] ++ x.toByteArray))
    | none =>  Hashable.hash (ByteArray.mk #[0])

end Std.Http.URI
