/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Mario Carneiro
-/
module

prelude
public import Init.Data.String.Basic
public import Init.Data.String.Termination
import Init.Data.ByteArray.Lemmas
import Init.Data.Char.Lemmas

/-!
# Modification operations on strings

This file contains operations on strings which modify the string, like `set` or `map`.
There will usually not be a `String.Slice` version of these operations.
-/

public section

namespace String

/--
Replaces the character at a specified position in a string with a new character.

If both the replacement character and the replaced character are 7-bit ASCII characters and the
string is not shared, then it is updated in-place and not copied.

Examples:
* `("abc".pos ⟨1⟩ (by decide)).set 'B' (by decide) = "aBc"`
* `("L∃∀N".pos ⟨4⟩ (by decide)).set 'X' (by decide) = "L∃XN"`
-/
@[extern "lean_string_utf8_set", expose]
def Pos.set {s : String} (p : s.Pos) (c : Char) (hp : p ≠ s.endPos) : String :=
  if hc : c.utf8Size = 1 ∧ (p.byte hp).utf8ByteSize isUTF8FirstByte_byte = 1 then
    .ofByteArray (s.toByteArray.set p.offset.byteIdx c.toUInt8 (p.byteIdx_lt_utf8ByteSize hp)) (by
      rw [ByteArray.set_eq_push_extract_append_extract, ← hc.2, utf8ByteSize_byte,
        ← Pos.byteIdx_offset_next]
      refine ByteArray.IsValidUTF8.append ?_ (p.next hp).isValid.isValidUTF8_extract_utf8ByteSize
      exact p.isValid.isValidUTF8_extract_zero.push hc.1)
  else
    (s.sliceTo p).copy ++ singleton c ++ (s.sliceFrom (p.next hp)).copy

theorem Pos.set_eq_append {s : String} {p : s.Pos} {c : Char} {hp} :
    p.set c hp = (s.sliceTo p).copy ++ singleton c ++ (s.sliceFrom (p.next hp)).copy := by
  rw [set]
  split
  · rename_i h
    simp [← toByteArray_inj, ByteArray.set_eq_push_extract_append_extract, Slice.toByteArray_copy,
      List.utf8Encode_singleton, String.utf8EncodeChar_eq_singleton h.1, utf8ByteSize_byte ▸ h.2]
  · rfl

theorem Pos.Raw.IsValid.set_of_le {s : String} {p : s.Pos} {c : Char} {hp : p ≠ s.endPos}
    {q : Pos.Raw} (hq : q.IsValid s) (hpq : q ≤ p.offset) : q.IsValid (p.set c hp) := by
  rw [Pos.set_eq_append, String.append_assoc]
  apply append_right
  rw [isValid_copy_iff, isValidForSlice_stringSliceTo]
  exact ⟨hpq, hq⟩

/-- Given a valid position in a string, obtain the corresponding position after setting a character on
that string, provided that the position was before the changed position. -/
@[inline]
def Pos.toSetOfLE {s : String} (q p : s.Pos) (c : Char) (hp : p ≠ s.endPos)
    (hpq : q ≤ p) : (p.set c hp).Pos where
  offset := q.offset
  isValid := q.isValid.set_of_le hpq

@[simp]
theorem Pos.offset_toSetOfLE {s : String} {q p : s.Pos} {c : Char} {hp : p ≠ s.endPos}
    {hpq : q ≤ p} : (q.toSetOfLE p c hp hpq).offset = q.offset := (rfl)

theorem Pos.Raw.isValid_add_char_set {s : String} {p : s.Pos} {c : Char} {hp} :
    (p.offset + c).IsValid (p.set c hp) :=
  Pos.set_eq_append ▸ IsValid.append_right (isValid_of_eq_rawEndPos (by simp)) _

/-- The position just after the position that changed in a `Pos.set` call. -/
@[inline]
def Pos.pastSet {s : String} (p : s.Pos) (c : Char) (hp) : (p.set c hp).Pos where
  offset := p.offset + c
  isValid := Pos.Raw.isValid_add_char_set

@[simp]
theorem Pos.offset_pastSet {s : String} {p : s.Pos} {c : Char} {hp} :
    (p.pastSet c hp).offset = p.offset + c := (rfl)

@[inline]
def Pos.appendRight {s : String} (p : s.Pos) (t : String) : (s ++ t).Pos where
  offset := p.offset
  isValid := p.isValid.append_right t

theorem Pos.splits_pastSet {s : String} {p : s.Pos} {c : Char} {hp} :
    (p.pastSet c hp).Splits ((s.sliceTo p).copy ++ singleton c) (s.sliceFrom (p.next hp)).copy where
  eq_append := set_eq_append
  offset_eq_rawEndPos := by simp

theorem remainingBytes_pastSet {s : String} {p : s.Pos} {c : Char} {hp} :
    (p.pastSet c hp).remainingBytes = (p.next hp).remainingBytes := by
  rw [(p.next hp).splits.remainingBytes_eq, p.splits_pastSet.remainingBytes_eq]

/--
Replaces the character at position `p` in the string `s` with the result of applying `f` to that
character.

If both the replacement character and the replaced character are 7-bit ASCII characters and the
string is not shared, then it is updated in-place and not copied.

Examples:
* `("abc".pos ⟨1⟩ (by decide)).modify Char.toUpper (by decide) = "aBc"`
-/
@[inline]
def Pos.modify {s : String} (p : s.Pos) (f : Char → Char) (hp : p ≠ s.endPos) :
    String :=
  p.set (f <| p.get hp) hp

theorem Pos.Raw.IsValid.modify_of_le {s : String} {p : s.Pos} {f : Char → Char}
    {hp : p ≠ s.endPos} {q : Pos.Raw} (hq : q.IsValid s) (hpq : q ≤ p.offset) :
    q.IsValid (p.modify f hp) :=
  set_of_le hq hpq

/-- Given a valid position in a string, obtain the corresponding position after modifying a character
in that string, provided that the position was before the changed position. -/
@[inline]
def Pos.toModifyOfLE {s : String} (q p : s.Pos) (f : Char → Char)
    (hp : p ≠ s.endPos) (hpq : q ≤ p) : (p.modify f hp).Pos where
  offset := q.offset
  isValid := q.isValid.modify_of_le hpq

@[simp]
theorem Pos.offset_toModifyOfLE {s : String} {q p : s.Pos} {f : Char → Char}
    {hp : p ≠ s.endPos} {hpq : q ≤ p} : (q.toModifyOfLE p f hp hpq).offset = q.offset := (rfl)

/-- The position just after the position that was modified in a `Pos.modify` call. -/
@[inline]
def Pos.pastModify {s : String} (p : s.Pos) (f : Char → Char)
    (hp : p ≠ s.endPos) : (p.modify f hp).Pos :=
  p.pastSet _ _

theorem remainingBytes_pastModify {s : String} {p : s.Pos} {f : Char → Char} {hp} :
    (p.pastModify f hp).remainingBytes = (p.next hp).remainingBytes :=
  remainingBytes_pastSet

/--
Replaces the character at a specified position in a string with a new character. If the position is
invalid, the string is returned unchanged.

If both the replacement character and the replaced character are 7-bit ASCII characters and the
string is not shared, then it is updated in-place and not copied.

This is a legacy function. The recommended alternative is `String.Pos.set`, combined with
`String.pos` or another means of obtaining a `String.Pos`.

Examples:
* `"abc".set ⟨1⟩ 'B' = "aBc"`
* `"abc".set ⟨3⟩ 'D' = "abc"`
* `"L∃∀N".set ⟨4⟩ 'X' = "L∃XN"`
* `"L∃∀N".set ⟨2⟩ 'X' = "L∃∀N"` because `'∃'` is a multi-byte character, so the byte index `2` is an
  invalid position.
-/
@[extern "lean_string_utf8_set", expose]
def Pos.Raw.set : String → (@& Pos.Raw) → Char → String
  | s, i, c => ofList (Pos.Raw.utf8SetAux c s.toList 0 i)

@[extern "lean_string_utf8_set", expose, deprecated Pos.Raw.set (since := "2025-10-14")]
def set : String → (@& Pos.Raw) → Char → String
  | s, i, c => ofList (Pos.Raw.utf8SetAux c s.toList 0 i)

/--
Replaces the character at position `p` in the string `s` with the result of applying `f` to that
character. If `p` is an invalid position, the string is returned unchanged.

If both the replacement character and the replaced character are 7-bit ASCII characters and the
string is not shared, then it is updated in-place and not copied.

This is a legacy function. The recommended alternative is `String.Pos.set`, combined with
`String.pos` or another means of obtaining a `String.Pos`.

Examples:
* `"abc".modify ⟨1⟩ Char.toUpper = "aBc"`
* `"abc".modify ⟨3⟩ Char.toUpper = "abc"`
-/
@[expose]
def Pos.Raw.modify (s : String) (i : Pos.Raw) (f : Char → Char) : String :=
  i.set s (f (i.get s))

@[expose, inherit_doc Pos.Raw.modify, deprecated Pos.Raw.modify (since := "2025-10-10")]
def modify (s : String) (i : Pos.Raw) (f : Char → Char) : String :=
  i.set s (f (i.get s))

@[specialize] def mapAux (f : Char → Char) (s : String) (p : s.Pos) : String :=
  if h : p = s.endPos then
    s
  else
    mapAux f (p.modify f h) (p.pastModify f h)
termination_by p.remainingBytes
decreasing_by all_goals sorry -- TODO: restore after bootstrap

/--
Applies the function `f` to every character in a string, returning a string that contains the
resulting characters.

Examples:
 * `"abc123".map Char.toUpper = "ABC123"`
 * `"".map Char.toUpper = ""`
-/
@[inline] def map (f : Char → Char) (s : String) : String :=
  mapAux f s s.startPos

/--
Replaces each character in `s` with the result of applying `Char.toUpper` to it.

`Char.toUpper` has no effect on characters outside of the range `'a'`–`'z'`.

Examples:
* `"orange".toUpper = "ORANGE"`
* `"abc123".toUpper = "ABC123"`
-/
@[inline] def toUpper (s : String) : String :=
  s.map Char.toUpper

/--
Replaces each character in `s` with the result of applying `Char.toLower` to it.

`Char.toLower` has no effect on characters outside of the range `'A'`–`'Z'`.

Examples:
* `"ORANGE".toLower = "orange"`
* `"Orange".toLower = "orange"`
* `"ABc123".toLower = "abc123"`
-/
@[inline] def toLower (s : String) : String :=
  s.map Char.toLower

/--
Replaces the first character in `s` with the result of applying `Char.toUpper` to it. Returns the
empty string if the string is empty.

`Char.toUpper` has no effect on characters outside of the range `'a'`–`'z'`.

Examples:
* `"orange".capitalize = "Orange"`
* `"ORANGE".capitalize = "ORANGE"`
* `"".capitalize = ""`
-/
@[inline] def capitalize (s : String) : String :=
  (0 : Pos.Raw).set s <| (0 : Pos.Raw).get s |>.toUpper

@[export lean_string_capitalize]
def Internal.capitalizeImpl (s : String) : String :=
  String.capitalize s

/--
Replaces the first character in `s` with the result of applying `Char.toLower` to it. Returns the
empty string if the string is empty.

`Char.toLower` has no effect on characters outside of the range `'A'`–`'Z'`.

Examples:
* `"Orange".decapitalize = "orange"`
* `"ORANGE".decapitalize = "oRANGE"`
* `"".decapitalize = ""`
-/
@[inline] def decapitalize (s : String) :=
  (0 : Pos.Raw).set s <| (0 : Pos.Raw).get s |>.toLower

end String
