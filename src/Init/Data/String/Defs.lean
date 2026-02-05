/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Mario Carneiro
-/
module

prelude
public import Init.Data.String.PosRaw
import Init.Data.ByteArray.Lemmas
import Init.Omega

/-!
# Preliminary developments for strings

This file contains the material about strings which we can write down without the results in
`Init.Data.String.Decode`, i.e., without knowing about the bijection between `String` and
`List Char` given by UTF-8 decoding and encoding.

Note that this file, despite being called `Defs`, contains quite a few lemmas.
-/

public section

@[simp]
theorem List.utf8Encode_nil : List.utf8Encode [] = ByteArray.empty := by simp [utf8Encode]

theorem List.utf8Encode_singleton {c : Char} : [c].utf8Encode = (String.utf8EncodeChar c).toByteArray := by
  simp [utf8Encode]

@[simp]
theorem List.utf8Encode_append {l l' : List Char} :
    (l ++ l').utf8Encode = l.utf8Encode ++ l'.utf8Encode := by
  simp [utf8Encode]

theorem List.utf8Encode_cons {c : Char} {l : List Char} : (c :: l).utf8Encode = [c].utf8Encode ++ l.utf8Encode := by
  rw [← singleton_append, List.utf8Encode_append]

@[simp]
theorem String.utf8EncodeChar_ne_nil {c : Char} : String.utf8EncodeChar c ≠ [] := by
  fun_cases String.utf8EncodeChar with simp

@[simp]
theorem List.utf8Encode_eq_empty {l : List Char} : l.utf8Encode = ByteArray.empty ↔ l = [] := by
  simp [utf8Encode, ← List.eq_nil_iff_forall_not_mem]

theorem ByteArray.isValidUTF8_utf8Encode {l : List Char} : IsValidUTF8 l.utf8Encode :=
  .intro l rfl

@[simp]
theorem ByteArray.isValidUTF8_empty : IsValidUTF8 ByteArray.empty :=
  .intro [] (by simp)

theorem Char.isValidUTF8_toByteArray_utf8EncodeChar {c : Char} :
    ByteArray.IsValidUTF8 (String.utf8EncodeChar c).toByteArray :=
  .intro [c] (by simp [List.utf8Encode_singleton])

theorem ByteArray.IsValidUTF8.append {b b' : ByteArray} (h : IsValidUTF8 b) (h' : IsValidUTF8 b') :
    IsValidUTF8 (b ++ b') := by
  rcases h with ⟨m, rfl⟩
  rcases h' with ⟨m', rfl⟩
  exact .intro (m ++ m') (by simp)

/--
Decodes an array of bytes that encode a string as [UTF-8](https://en.wikipedia.org/wiki/UTF-8) into
the corresponding string.
-/
@[inline, expose]
def String.fromUTF8 (a : @& ByteArray) (h : a.IsValidUTF8) : String :=
  .ofByteArray a h

/--
Encodes a string in UTF-8 as an array of bytes.
-/
@[extern "lean_string_to_utf8"]
def String.toUTF8 (a : @& String) : ByteArray :=
  a.toByteArray

@[simp] theorem String.toUTF8_eq_toByteArray {s : String} : s.toUTF8 = s.toByteArray := (rfl)

@[simp] theorem String.toByteArray_empty : "".toByteArray = ByteArray.empty := (rfl)

/--
Appends two strings. Usually accessed via the `++` operator.

The internal implementation will perform destructive updates if the string is not shared.

Examples:
 * `"abc".append "def" = "abcdef"`
 * `"abc" ++ "def" = "abcdef"`
 * `"" ++ "" = ""`
-/
@[extern "lean_string_append", expose]
def String.append (s : String) (t : @& String) : String where
  toByteArray := s.toByteArray ++ t.toByteArray
  isValidUTF8 := s.isValidUTF8.append t.isValidUTF8

instance : Append String where
  append s t := s.append t

@[simp]
theorem String.toByteArray_append {s t : String} : (s ++ t).toByteArray = s.toByteArray ++ t.toByteArray := (rfl)

theorem String.toByteArray_inj {s t : String} : s.toByteArray = t.toByteArray ↔ s = t := by
  refine ⟨fun h => ?_, (· ▸ rfl)⟩
  rcases s with ⟨s⟩
  rcases t with ⟨t⟩
  subst h
  rfl

@[simp] theorem String.toByteArray_ofList {l : List Char} : (String.ofList l).toByteArray = l.utf8Encode := by
  simp [String.ofList]

@[deprecated String.toByteArray_ofList (since := "2025-10-30")]
theorem List.toByteArray_asString {l : List Char} : (String.ofList l).toByteArray = l.utf8Encode :=
  String.toByteArray_ofList

theorem String.exists_eq_ofList (s : String) :
    ∃ l : List Char, s = String.ofList l := by
  rcases s with ⟨_, ⟨l, rfl⟩⟩
  refine ⟨l, by simp [← String.toByteArray_inj]⟩

@[deprecated String.exists_eq_ofList (since := "2025-10-30")]
theorem String.exists_eq_asString (s : String) :
    ∃ l : List Char, s = String.ofList l :=
  s.exists_eq_ofList

@[simp]
theorem String.utf8ByteSize_empty : "".utf8ByteSize = 0 := (rfl)

@[simp]
theorem String.utf8ByteSize_append {s t : String} :
    (s ++ t).utf8ByteSize = s.utf8ByteSize + t.utf8ByteSize := by
  simp [utf8ByteSize]

@[simp]
theorem String.size_toByteArray {s : String} : s.toByteArray.size = s.utf8ByteSize := rfl

@[simp]
theorem String.toByteArray_push {s : String} {c : Char} : (s.push c).toByteArray = s.toByteArray ++ [c].utf8Encode := by
  simp [push]

namespace String

/-- The start position of the string, as a `String.Pos.Raw.` -/
def rawStartPos (_s : String) : String.Pos.Raw :=
  0

@[simp]
theorem rawStartPos_eq {s : String} : s.rawStartPos = 0 := (rfl)

@[simp]
theorem byteIdx_rawEndPos {s : String} : s.rawEndPos.byteIdx = s.utf8ByteSize := rfl

@[deprecated byteIdx_rawEndPos (since := "2025-10-20")]
theorem byteIdx_endPos {s : String} : s.rawEndPos.byteIdx = s.utf8ByteSize := rfl

@[simp]
theorem utf8ByteSize_ofByteArray {b : ByteArray} {h} :
    (String.ofByteArray b h).utf8ByteSize = b.size := rfl

@[simp]
theorem toByteArray_singleton {c : Char} : (String.singleton c).toByteArray = [c].utf8Encode := by
  simp [singleton]

theorem singleton_eq_ofList {c : Char} : String.singleton c = String.ofList [c] := by
  simp [← String.toByteArray_inj]

@[deprecated singleton_eq_ofList (since := "2025-10-30")]
theorem singleton_eq_asString {c : Char} : String.singleton c = String.ofList [c] :=
  singleton_eq_ofList

@[simp]
theorem append_singleton {s : String} {c : Char} : s ++ singleton c = s.push c := by
  simp [← toByteArray_inj]

@[simp]
theorem append_left_inj {s₁ s₂ : String} (t : String) :
    s₁ ++ t = s₂ ++ t ↔ s₁ = s₂ := by
  simp [← toByteArray_inj]

theorem append_assoc {s₁ s₂ s₃ : String} : s₁ ++ s₂ ++ s₃ = s₁ ++ (s₂ ++ s₃) := by
  simp [← toByteArray_inj, ByteArray.append_assoc]

@[simp]
theorem utf8ByteSize_eq_zero_iff {s : String} : s.utf8ByteSize = 0 ↔ s = "" := by
  refine ⟨fun h => ?_, fun h => h ▸ utf8ByteSize_empty⟩
  simpa [← toByteArray_inj, ← ByteArray.size_eq_zero_iff] using h

theorem rawEndPos_eq_zero_iff {b : String} : b.rawEndPos = 0 ↔ b = "" := by
  simp

@[deprecated rawEndPos_eq_zero_iff (since := "2025-10-20")]
theorem endPos_eq_zero_iff {b : String} : b.rawEndPos = 0 ↔ b = "" :=
  rawEndPos_eq_zero_iff

/--
Adds multiple repetitions of a character to the end of a string.

Returns `s`, with `n` repetitions of `c` at the end. Internally, the implementation repeatedly calls
`String.push`, so the string is modified in-place if there is a unique reference to it.

Examples:
 * `"indeed".pushn '!' 2 = "indeed!!"`
 * `"indeed".pushn '!' 0 = "indeed"`
 * `"".pushn ' ' 4 = "    "`
-/
@[inline] def pushn (s : String) (c : Char) (n : Nat) : String :=
  n.repeat (fun s => s.push c) s

theorem pushn_eq_repeat_push {s : String} {c : Char} {n : Nat} :
    s.pushn c n = n.repeat (fun s => s.push c) s := (rfl)

@[export lean_string_pushn]
def Internal.pushnImpl (s : String) (c : Char) (n : Nat) : String :=
  String.pushn s c n

/--
Checks whether a string is empty.

Empty strings are equal to `""` and have length and end position `0`.

Examples:
 * `"".isEmpty = true`
 * `"empty".isEmpty = false`
 * `" ".isEmpty = false`
-/
@[inline] def isEmpty (s : String) : Bool :=
  s.utf8ByteSize == 0

@[export lean_string_isempty]
def Internal.isEmptyImpl (s : String) : Bool :=
  String.isEmpty s

/--
Appends all the strings in a list of strings, in order.

Use `String.intercalate` to place a separator string between the strings in a list.

Examples:
 * `String.join ["gr", "ee", "n"] = "green"`
 * `String.join ["b", "", "l", "", "ue"] = "blue"`
 * `String.join [] = ""`
-/
@[inline] def join (l : List String) : String :=
  l.foldl (fun r s => r ++ s) ""

/--
Appends the strings in a list of strings, placing the separator `s` between each pair.

Examples:
 * `", ".intercalate ["red", "green", "blue"] = "red, green, blue"`
 * `" and ".intercalate ["tea", "coffee"] = "tea and coffee"`
 * `" | ".intercalate ["M", "", "N"] = "M |  | N"`
-/
def intercalate (s : String) : List String → String
  | []      => ""
  | a :: as => go a s as
where go (acc : String) (s : String) : List String → String
  | a :: as => go (acc ++ s ++ a) s as
  | []      => acc

@[export lean_string_intercalate]
def Internal.intercalateImpl (s : String) : List String → String :=
  String.intercalate s

/--
Predicate for validity of positions inside a `String`.

There are multiple equivalent definitions for validity.

We say that a position is valid if the string obtained by taking all of the bytes up to, but
excluding, the given position, is valid UTF-8; see `Pos.isValid_iff_isValidUTF8_extract_zero`.

Similarly, a position is valid if the string obtained by taking all of the bytes starting at the
given position is valid UTF-8; see `Pos.isValid_iff_isValidUTF8_extract_utf8ByteSize`.

An equivalent condition is that the position is the length of the UTF-8 encoding of
some prefix of the characters of the string; see `Pos.isValid_iff_exists_append` and
`Pos.isValid_iff_exists_take_data`.

Another equivalent condition that can be checked efficiently is that the position is either the
end position or strictly smaller than the end position and the byte at the position satisfies
`UInt8.IsUTF8FirstByte`; see `Pos.isValid_iff_isUTF8FirstByte`.

Examples:
 * `String.Pos.IsValid "abc" ⟨0⟩`
 * `String.Pos.IsValid "abc" ⟨1⟩`
 * `String.Pos.IsValid "abc" ⟨3⟩`
 * `¬ String.Pos.IsValid "abc" ⟨4⟩`
 * `String.Pos.IsValid "𝒫(A)" ⟨0⟩`
 * `¬ String.Pos.IsValid "𝒫(A)" ⟨1⟩`
 * `¬ String.Pos.IsValid "𝒫(A)" ⟨2⟩`
 * `¬ String.Pos.IsValid "𝒫(A)" ⟨3⟩`
 * `String.Pos.IsValid "𝒫(A)" ⟨4⟩`
-/
structure Pos.Raw.IsValid (s : String) (off : String.Pos.Raw) : Prop where private mk ::
  le_rawEndPos : off ≤ s.rawEndPos
  isValidUTF8_extract_zero : (s.toByteArray.extract 0 off.byteIdx).IsValidUTF8

theorem Pos.Raw.IsValid.le_utf8ByteSize {s : String} {off : String.Pos.Raw} (h : off.IsValid s) :
    off.byteIdx ≤ s.utf8ByteSize := by
  simpa [Pos.Raw.le_iff] using h.le_rawEndPos

theorem Pos.Raw.isValid_iff_isValidUTF8_extract_zero {s : String} {p : Pos.Raw} :
    p.IsValid s ↔ p ≤ s.rawEndPos ∧ (s.toByteArray.extract 0 p.byteIdx).IsValidUTF8 :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

@[deprecated le_rawEndPos (since := "2025-10-20")]
theorem Pos.Raw.IsValid.le_endPos {s : String} {off : String.Pos.Raw} (h : off.IsValid s) :
    off ≤ s.rawEndPos :=
  h.le_rawEndPos

@[simp]
theorem Pos.Raw.isValid_zero {s : String} : (0 : Pos.Raw).IsValid s where
  le_rawEndPos := by simp [Pos.Raw.le_iff]
  isValidUTF8_extract_zero := by simp

@[simp]
theorem Pos.Raw.isValid_rawEndPos {s : String} : s.rawEndPos.IsValid s where
  le_rawEndPos := by simp
  isValidUTF8_extract_zero := by simp [← size_toByteArray, s.isValidUTF8]

theorem Pos.Raw.isValid_of_eq_rawEndPos {s : String} {p : Pos.Raw} (h : p = s.rawEndPos) :
    p.IsValid s := by
  subst h
  exact isValid_rawEndPos

@[simp]
theorem Pos.Raw.isValid_empty_iff {p : Pos.Raw} : p.IsValid "" ↔ p = 0 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨h₁, h₂⟩
    simp only [le_iff, byteIdx_rawEndPos, utf8ByteSize_empty, Nat.le_zero_eq] at h₁
    ext
    omega
  · rintro rfl
    simp

/--
A `Pos s` is a byte offset in `s` together with a proof that this position is at a UTF-8
character boundary.
-/
@[ext]
structure Pos (s : String) where
  /-- The underlying byte offset of the `Pos`. -/
  offset : Pos.Raw
  /-- The proof that `offset` is valid for the string `s`. -/
  isValid : offset.IsValid s
deriving @[expose] DecidableEq

/-- The start position of `s`, as an `s.Pos`. -/
@[inline, expose]
def startPos (s : String) : s.Pos where
  offset := 0
  isValid := by simp

@[simp]
theorem offset_startPos {s : String} : s.startPos.offset = 0 := (rfl)

instance {s : String} : Inhabited s.Pos where
  default := s.startPos

/-- The past-the-end position of `s`, as an `s.Pos`. -/
@[inline, expose]
def endPos (s : String) : s.Pos where
  offset := s.rawEndPos
  isValid := by simp

@[simp]
theorem offset_endPos {s : String} : s.endPos.offset = s.rawEndPos := (rfl)

instance {s : String} : LE s.Pos where
  le l r := l.offset ≤ r.offset

instance {s : String} : LT s.Pos where
  lt l r := l.offset < r.offset

theorem Pos.le_iff {s : String} {l r : s.Pos} : l ≤ r ↔ l.offset ≤ r.offset :=
  Iff.rfl

theorem Pos.lt_iff {s : String} {l r : s.Pos} : l < r ↔ l.offset < r.offset :=
  Iff.rfl

instance {s : String} (l r : s.Pos) : Decidable (l ≤ r) :=
  decidable_of_iff' _ Pos.le_iff

instance {s : String} (l r : s.Pos) : Decidable (l < r) :=
decidable_of_iff' _ Pos.lt_iff

/--
A region or slice of some underlying string.

A slice consists of a string together with the start and end byte positions of a region of
interest. Actually extracting a substring requires copying and memory allocation, while many
slices of the same underlying string may exist with very little overhead. While this could be
achieved by tracking the bounds by hand, the slice API is much more convenient.

`String.Slice` bundles proofs to ensure that the start and end positions always delineate a valid
string. For this reason, it should be preferred over `Substring.Raw`.
-/
structure Slice where
  /-- The underlying strings. -/
  str : String
  /-- The byte position of the start of the string slice. -/
  startInclusive : str.Pos
  /-- The byte position of the end of the string slice. -/
  endExclusive : str.Pos
  /-- The slice is not degenerate (but it may be empty). -/
  startInclusive_le_endExclusive : startInclusive ≤ endExclusive

instance : Inhabited Slice where
  default := ⟨"", "".startPos, "".startPos, by simp [Pos.le_iff]⟩

/--
Returns a slice that contains the entire string.
-/
@[inline, expose] -- expose for the defeq `s.toSlice.str = s`.
def toSlice (s : String) : Slice where
  str := s
  startInclusive := s.startPos
  endExclusive := s.endPos
  startInclusive_le_endExclusive := by simp [Pos.le_iff, Pos.Raw.le_iff]

instance : Coe String String.Slice where
  coe := String.toSlice

@[simp]
theorem startInclusive_toSlice {s : String} : s.toSlice.startInclusive = s.startPos := rfl

@[simp]
theorem endExclusive_toSlice {s : String} : s.toSlice.endExclusive = s.endPos := rfl

@[simp]
theorem str_toSlice {s : String} : s.toSlice.str = s := rfl

/-- The number of bytes of the UTF-8 encoding of the string slice. -/
@[expose, inline]
def Slice.utf8ByteSize (s : Slice) : Nat :=
  s.startInclusive.offset.byteDistance s.endExclusive.offset

theorem Slice.utf8ByteSize_eq {s : Slice} :
    s.utf8ByteSize = s.endExclusive.offset.byteIdx - s.startInclusive.offset.byteIdx := (rfl)

instance : HAdd Pos.Raw Slice Pos.Raw where
  hAdd p s := { byteIdx := p.byteIdx + s.utf8ByteSize }

instance : HAdd Slice Pos.Raw Pos.Raw where
  hAdd s p := { byteIdx := s.utf8ByteSize + p.byteIdx }

instance : HSub Pos.Raw Slice Pos.Raw where
  hSub p s := { byteIdx := p.byteIdx - s.utf8ByteSize }

@[simp]
theorem Pos.Raw.byteIdx_add_slide {p : Pos.Raw} {s : Slice} :
    (p + s).byteIdx = p.byteIdx + s.utf8ByteSize := rfl

@[simp]
theorem Pos.Raw.byteIdx_slice_add {s : Slice} {p : Pos.Raw} :
    (s + p).byteIdx = s.utf8ByteSize + p.byteIdx := rfl

@[simp]
theorem Pos.Raw.byteIdx_sub_slice {p : Pos.Raw} {s : Slice} :
    (p - s).byteIdx = p.byteIdx - s.utf8ByteSize := rfl

/-- The end position of a slice, as a `Pos.Raw`. -/
@[expose, inline]
def Slice.rawEndPos (s : Slice) : Pos.Raw where
  byteIdx := s.utf8ByteSize

@[simp]
theorem Slice.byteIdx_rawEndPos {s : Slice} : s.rawEndPos.byteIdx = s.utf8ByteSize := (rfl)

/-- Criterion for validity of positions in string slices. -/
structure Pos.Raw.IsValidForSlice (s : Slice) (p : Pos.Raw) : Prop where
  le_rawEndPos : p ≤ s.rawEndPos
  isValid_offsetBy : (p.offsetBy s.startInclusive.offset).IsValid s.str

theorem Pos.Raw.IsValidForSlice.le_utf8ByteSize {s : Slice} {p : Pos.Raw}
    (h : p.IsValidForSlice s) : p.byteIdx ≤ s.utf8ByteSize := by
  simpa [Pos.Raw.le_iff] using h.le_rawEndPos

/--
Accesses the indicated byte in the UTF-8 encoding of a string slice.

At runtime, this function is implemented by efficient, constant-time code.
-/
@[inline, expose]
def Slice.getUTF8Byte (s : Slice) (p : Pos.Raw) (h : p < s.rawEndPos) : UInt8 :=
  s.str.getUTF8Byte (p.offsetBy s.startInclusive.offset) (by
    have := s.endExclusive.isValid.le_rawEndPos
    simp only [Pos.Raw.lt_iff, byteIdx_rawEndPos, utf8ByteSize_eq, Pos.Raw.le_iff, byteIdx_rawEndPos,
      Pos.Raw.byteIdx_offsetBy] at *
    omega)

/--
Accesses the indicated byte in the UTF-8 encoding of the string slice, or panics if the position
is out-of-bounds.
-/
@[expose]
def Slice.getUTF8Byte! (s : Slice) (p : String.Pos.Raw) : UInt8 :=
  if h : p < s.rawEndPos then
    s.getUTF8Byte p h
  else
    panic! "String slice access is out of bounds."

/--
A `Slice.Pos s` is a byte offset in `s` together with a proof that this position is at a UTF-8
character boundary.
-/
@[ext]
structure Slice.Pos (s : Slice) where
  /-- The underlying byte offset of the `Slice.Pos`. -/
  offset : String.Pos.Raw
  /-- The proof that `offset` is valid for the string slice `s`. -/
  isValidForSlice : offset.IsValidForSlice s
deriving @[expose] DecidableEq

/-- The start position of `s`, as an `s.Pos`. -/
@[inline, expose]
def Slice.startPos (s : Slice) : s.Pos where
  offset := 0
  isValidForSlice := ⟨by simp [Pos.Raw.le_iff], by simpa using s.startInclusive.isValid⟩

@[simp]
theorem Slice.offset_startPos {s : Slice} : s.startPos.offset = 0 := (rfl)

instance {s : Slice} : Inhabited s.Pos where
  default := s.startPos

@[simp]
theorem Slice.offset_startInclusive_add_self {s : Slice} :
    s.startInclusive.offset + s = s.endExclusive.offset := by
  have := s.startInclusive_le_endExclusive
  simp_all [String.Pos.Raw.ext_iff, Pos.le_iff, Pos.Raw.le_iff, utf8ByteSize_eq]

@[simp]
theorem Pos.Raw.offsetBy_rawEndPos_left {p : Pos.Raw} {s : String} :
    s.rawEndPos.offsetBy p = p + s := by
  simp [Pos.Raw.ext_iff]

@[simp]
theorem Pos.Raw.offsetBy_rawEndPos_right {p : Pos.Raw} {s : String} :
    p.offsetBy s.rawEndPos = s + p := by
  simp [Pos.Raw.ext_iff]

@[simp]
theorem Pos.Raw.offsetBy_sliceRawEndPos_left {p : Pos.Raw} {s : Slice} :
    s.rawEndPos.offsetBy p = p + s := by
  simp [Pos.Raw.ext_iff]

@[simp]
theorem Pos.Raw.offsetBy_sliceRawEndPos_right {p : Pos.Raw} {s : Slice} :
    p.offsetBy s.rawEndPos = s + p := by
  simp [Pos.Raw.ext_iff]

@[simp]
theorem Pos.Raw.isValidForSlice_rawEndPos {s : Slice} : (s.rawEndPos).IsValidForSlice s where
  le_rawEndPos := by simp
  isValid_offsetBy := by simpa using s.endExclusive.isValid

theorem Pos.Raw.isValidForSlice_of_eq_rawEndPos {p : Pos.Raw} {s : Slice} (h : p = s.rawEndPos) :
    p.IsValidForSlice s := by
  subst h; simp

/-- The past-the-end position of `s`, as an `s.Pos`. -/
@[inline, expose]
def Slice.endPos (s : Slice) : s.Pos where
  offset := s.rawEndPos
  isValidForSlice := Pos.Raw.isValidForSlice_rawEndPos

@[simp]
theorem Slice.offset_endPos {s : Slice} : s.endPos.offset = s.rawEndPos := (rfl)

instance {s : Slice} : LE s.Pos where
  le l r := l.offset ≤ r.offset

instance {s : Slice} : LT s.Pos where
  lt l r := l.offset < r.offset

theorem Slice.Pos.le_iff {s : Slice} {l r : s.Pos} : l ≤ r ↔ l.offset ≤ r.offset :=
  Iff.rfl

theorem Slice.Pos.lt_iff {s : Slice} {l r : s.Pos} : l < r ↔ l.offset < r.offset :=
  Iff.rfl

instance {s : Slice} (l r : s.Pos) : Decidable (l ≤ r) :=
  decidable_of_iff' _ Slice.Pos.le_iff

instance {s : Slice} (l r : s.Pos) : Decidable (l < r) :=
  decidable_of_iff' _ Slice.Pos.lt_iff

/--
`pos.IsAtEnd` is just shorthand for `pos = s.endPos` that is easier to write if `s` is long.
-/
abbrev Pos.IsAtEnd {s : String} (pos : s.Pos) : Prop :=
  pos = s.endPos

@[simp]
theorem Pos.isAtEnd_iff {s : String} {pos : s.Pos} :
    pos.IsAtEnd ↔ pos = s.endPos := Iff.rfl

@[inline]
instance {s : String} {pos : s.Pos} : Decidable pos.IsAtEnd :=
  decidable_of_iff _ Pos.isAtEnd_iff

/--
`pos.IsAtEnd` is just shorthand for `pos = s.endPos` that is easier to write if `s` is long.
-/
abbrev Slice.Pos.IsAtEnd {s : Slice} (pos : s.Pos) : Prop :=
  pos = s.endPos

@[simp]
theorem Slice.Pos.isAtEnd_iff {s : Slice} {pos : s.Pos} :
    pos.IsAtEnd ↔ pos = s.endPos := Iff.rfl

@[inline]
instance {s : Slice} {pos : s.Pos} : Decidable pos.IsAtEnd :=
  decidable_of_iff _ Slice.Pos.isAtEnd_iff

/-- Returns the byte at a position in a slice that is not the end position. -/
@[inline, expose]
def Slice.Pos.byte {s : Slice} (pos : s.Pos) (h : pos ≠ s.endPos) : UInt8 :=
  s.getUTF8Byte pos.offset (by
    have := pos.isValidForSlice.le_rawEndPos
    simp_all [Pos.ext_iff, String.Pos.Raw.ext_iff, Pos.Raw.le_iff, Pos.Raw.lt_iff]
    omega)

@[simp] theorem default_eq : default = "" := rfl

theorem push_eq_append (c : Char) : String.push s c = s ++ singleton c := by
  simp

/--
Checks whether a slice is empty.

Empty slices have {name}`utf8ByteSize` {lean}`0`.

Examples:
 * {lean}`"".toSlice.isEmpty = true`
 * {lean}`" ".toSlice.isEmpty = false`
-/
@[inline]
def Slice.isEmpty (s : Slice) : Bool := s.utf8ByteSize == 0

@[simp]
theorem Slice.Pos.le_refl {s : Slice} (p : s.Pos) : p ≤ p := by
  simp [le_iff]

theorem Slice.Pos.lt_trans {s : Slice} {p q r : s.Pos} : p < q → q < r → p < r := by
  simpa [Pos.lt_iff, Pos.Raw.lt_iff] using Nat.lt_trans

@[simp]
theorem Pos.le_refl {s : String} (p : s.Pos) : p ≤ p := by
  simp [Pos.le_iff]

theorem Pos.lt_trans {s : String} {p q r : s.Pos} : p < q → q < r → p < r := by
  simpa [Pos.lt_iff, Pos.Raw.lt_iff] using Nat.lt_trans

@[deprecated String.toRawSubstring (since := "2025-11-18")]
def toSubstring (s : String) : Substring.Raw :=
  s.toRawSubstring

@[deprecated String.toRawSubstring' (since := "2025-11-18")]
def toSubstring' (s : String) : Substring.Raw :=
  s.toRawSubstring'

@[deprecated String.Pos (since := "2025-11-24")]
abbrev ValidPos (s : String) : Type :=
  s.Pos

@[deprecated String.startPos (since := "2025-11-24")]
abbrev startValidPos (s : String) : s.Pos :=
  s.startPos

@[deprecated String.endPos (since := "2025-11-24")]
abbrev endValidPos (s : String) : s.Pos :=
  s.endPos

@[deprecated String.toByteArray (since := "2025-11-24")]
abbrev String.bytes (s : String) : ByteArray :=
  s.toByteArray

end String
