/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Mario Carneiro
-/
module

prelude
public import Init.Data.String.Basic
import Init.Data.ByteArray.Lemmas

/-!
# Modification operations on strings

This file
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
def ValidPos.set {s : String} (p : s.ValidPos) (c : Char) (hp : p ≠ s.endValidPos) : String :=
  if hc : c.utf8Size = 1 ∧ (p.byte hp).utf8ByteSize isUTF8FirstByte_byte = 1 then
    .ofByteArray (s.bytes.set p.offset.byteIdx c.toUInt8 (p.byteIdx_lt_utf8ByteSize hp)) (by
      rw [ByteArray.set_eq_push_extract_append_extract, ← hc.2, utf8ByteSize_byte,
        ← ValidPos.byteIdx_offset_next]
      refine ByteArray.IsValidUTF8.append ?_ (p.next hp).isValid.isValidUTF8_extract_utf8ByteSize
      exact p.isValid.isValidUTF8_extract_zero.push hc.1)
  else
    (s.replaceEnd p).copy ++ singleton c ++ (s.replaceStart (p.next hp)).copy

theorem ValidPos.set_eq_append {s : String} {p : s.ValidPos} {c : Char} {hp} :
    p.set c hp = (s.replaceEnd p).copy ++ singleton c ++ (s.replaceStart (p.next hp)).copy := by
  rw [set]
  split
  · rename_i h
    simp [← bytes_inj, ByteArray.set_eq_push_extract_append_extract, Slice.bytes_copy,
      List.utf8Encode_singleton, String.utf8EncodeChar_eq_singleton h.1, utf8ByteSize_byte ▸ h.2]
  · rfl

theorem Pos.Raw.IsValid.set_of_le {s : String} {p : s.ValidPos} {c : Char} {hp : p ≠ s.endValidPos}
    {q : Pos.Raw} (hq : q.IsValid s) (hpq : q ≤ p.offset) : q.IsValid (p.set c hp) := by
  rw [ValidPos.set_eq_append, String.append_assoc]
  apply append_right
  rw [isValid_copy_iff, isValidForSlice_stringReplaceEnd]
  exact ⟨hpq, hq⟩

/-- Given a valid position in a string, obtain the corresponding position after setting a character on
that string, provided that the position was before the changed position. -/
@[inline]
def ValidPos.toSetOfLE {s : String} (q p : s.ValidPos) (c : Char) (hp : p ≠ s.endValidPos)
    (hpq : q ≤ p) : (p.set c hp).ValidPos where
  offset := q.offset
  isValid := q.isValid.set_of_le hpq

@[simp]
theorem ValidPos.offset_toSetOfLE {s : String} {q p : s.ValidPos} {c : Char} {hp : p ≠ s.endValidPos}
    {hpq : q ≤ p} : (q.toSetOfLE p c hp hpq).offset = q.offset := (rfl)

/--
Replaces the character at position `p` in the string `s` with the result of applying `f` to that
character.

If both the replacement character and the replaced character are 7-bit ASCII characters and the
string is not shared, then it is updated in-place and not copied.

Examples:
* `("abc".pos ⟨1⟩ (by decide)).modify Char.toUpper (by decide) = "aBc"`
-/
def ValidPos.modify {s : String} (p : s.ValidPos) (f : Char → Char) (hp : p ≠ s.endValidPos) :
    String :=
  p.set (f <| p.get hp) hp

theorem Pos.Raw.IsValid.modify_of_le {s : String} {p : s.ValidPos} {f : Char → Char}
    {hp : p ≠ s.endValidPos} {q : Pos.Raw} (hq : q.IsValid s) (hpq : q ≤ p.offset) :
    q.IsValid (p.modify f hp) :=
  set_of_le hq hpq

/-- Given a valid position in a string, obtain the corresponding position after modifying a character
in that string, provided that the position was before the changed position. -/
def ValidPos.toModifyOfLE {s : String} (q p : s.ValidPos) (f : Char → Char)
    (hp : p ≠ s.endValidPos) (hpq : q ≤ p) : (p.modify f hp).ValidPos where
  offset := q.offset
  isValid := q.isValid.modify_of_le hpq

@[simp]
theorem ValidPos.offset_toModifyOfLE {s : String} {q p : s.ValidPos} {f : Char → Char}
    {hp : p ≠ s.endValidPos} {hpq : q ≤ p} : (q.toModifyOfLE p f hp hpq).offset = q.offset := (rfl)

/--
Replaces the character at a specified position in a string with a new character. If the position is
invalid, the string is returned unchanged.

If both the replacement character and the replaced character are 7-bit ASCII characters and the
string is not shared, then it is updated in-place and not copied.

This is a legacy function. The recommended alternative is `String.ValidPos.set`, combined with
`String.pos` or another means of obtaining a `String.ValidPos`.

Examples:
* `"abc".set ⟨1⟩ 'B' = "aBc"`
* `"abc".set ⟨3⟩ 'D' = "abc"`
* `"L∃∀N".set ⟨4⟩ 'X' = "L∃XN"`
* `"L∃∀N".set ⟨2⟩ 'X' = "L∃∀N"` because `'∃'` is a multi-byte character, so the byte index `2` is an
  invalid position.
-/
@[extern "lean_string_utf8_set", expose]
def Pos.Raw.set : String → (@& Pos.Raw) → Char → String
  | s, i, c => (Pos.Raw.utf8SetAux c s.data 0 i).asString

@[extern "lean_string_utf8_set", expose, deprecated Pos.Raw.set (since := "2025-10-14")]
def set : String → (@& Pos.Raw) → Char → String
  | s, i, c => (Pos.Raw.utf8SetAux c s.data 0 i).asString

/--
Replaces the character at position `p` in the string `s` with the result of applying `f` to that
character. If `p` is an invalid position, the string is returned unchanged.

If both the replacement character and the replaced character are 7-bit ASCII characters and the
string is not shared, then it is updated in-place and not copied.

This is a legacy function. The recommended alternative is `String.ValidPos.set`, combined with
`String.pos` or another means of obtaining a `String.ValidPos`.

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

-- This is just to keep the proof of `set_next_add` below from breaking; if that lemma goes away
-- or the proof is rewritten, it can be removed.
private noncomputable def utf8ByteSize' : String → Nat
  | s => go s.data
where
  go : List Char → Nat
  | []    => 0
  | c::cs => go cs + c.utf8Size

private theorem utf8ByteSize'_eq (s : String) : s.utf8ByteSize' = s.utf8ByteSize := by
  suffices ∀ l, utf8ByteSize'.go l = l.asString.utf8ByteSize by
    obtain ⟨m, rfl⟩ := s.exists_eq_asString
    rw [utf8ByteSize', this, asString_data]
  intro l
  induction l with
  | nil => simp [utf8ByteSize'.go]
  | cons c cs ih =>
    rw [utf8ByteSize'.go, ih, ← List.singleton_append, List.asString_append,
      utf8ByteSize_append, Nat.add_comm]
    congr
    rw [← size_bytes, List.bytes_asString, List.utf8Encode_singleton,
      List.size_toByteArray, length_utf8EncodeChar]

theorem set_next_add (s : String) (i : Pos.Raw) (c : Char) (b₁ b₂)
    (h : (i.next s).1 + b₁ = s.rawEndPos.1 + b₂) :
  (i.next (i.set s c)).1 + b₁ = (i.set s c).rawEndPos.1 + b₂ := by
  simp [Pos.Raw.next, Pos.Raw.get, Pos.Raw.set, rawEndPos, ← utf8ByteSize'_eq, utf8ByteSize'] at h ⊢
  rw [Nat.add_comm i.1, Nat.add_assoc] at h ⊢
  let rec foo : ∀ cs a b₁ b₂,
    (Pos.Raw.utf8GetAux cs a i).utf8Size + b₁ = utf8ByteSize'.go cs + b₂ →
    (Pos.Raw.utf8GetAux (Pos.Raw.utf8SetAux c cs a i) a i).utf8Size + b₁ = utf8ByteSize'.go (Pos.Raw.utf8SetAux c cs a i) + b₂
  | [], _, _, _, h => h
  | c'::cs, a, b₁, b₂, h => by
    unfold Pos.Raw.utf8SetAux
    apply iteInduction (motive := fun p => (Pos.Raw.utf8GetAux p a i).utf8Size + b₁ = utf8ByteSize'.go p + b₂) <;>
      intro h' <;> simp [Pos.Raw.utf8GetAux, h', utf8ByteSize'.go] at h ⊢
    next =>
      rw [Nat.add_assoc, Nat.add_left_comm] at h ⊢; rw [Nat.add_left_cancel h]
    next =>
      rw [Nat.add_assoc] at h ⊢
      refine foo cs (a + c') b₁ (c'.utf8Size + b₂) h
  exact foo s.data 0 _ _ h

theorem mapAux_lemma (s : String) (i : Pos.Raw) (c : Char) (h : ¬i.atEnd s) :
    (i.set s c).rawEndPos.1 - (i.next (i.set s c)).1 < s.rawEndPos.1 - i.1 := by
  suffices (i.set s c).rawEndPos.1 - (i.next (i.set s c)).1 = s.rawEndPos.1 - (i.next s).1 by
    rw [this]
    apply Nat.sub_lt_sub_left (Nat.gt_of_not_le (mt decide_eq_true h)) (Pos.Raw.lt_next ..)
  have := set_next_add s i c (s.rawEndPos.byteIdx - (i.next s).byteIdx) 0
  have := set_next_add s i c 0 ((i.next s).byteIdx - s.rawEndPos.byteIdx)
  omega

@[specialize] def mapAux (f : Char → Char) (i : Pos.Raw) (s : String) : String :=
  if h : i.atEnd s then s
  else
    let c := f (i.get s)
    have := mapAux_lemma s i c h
    let s := i.set s c
    mapAux f (i.next s) s
termination_by s.rawEndPos.1 - i.1

/--
Applies the function `f` to every character in a string, returning a string that contains the
resulting characters.

Examples:
 * `"abc123".map Char.toUpper = "ABC123"`
 * `"".map Char.toUpper = ""`
-/
@[inline] def map (f : Char → Char) (s : String) : String :=
  mapAux f 0 s

/--
In the string `s`, replaces all occurrences of `pattern` with `replacement`.

Examples:
* `"red green blue".replace "e" "" = "rd grn blu"`
* `"red green blue".replace "ee" "E" = "red grEn blue"`
* `"red green blue".replace "e" "E" = "rEd grEEn bluE"`
-/
def replace (s pattern replacement : String) : String :=
  if h : pattern.rawEndPos.1 = 0 then s
  else
    have hPatt := Nat.zero_lt_of_ne_zero h
    let rec loop (acc : String) (accStop pos : String.Pos.Raw) :=
      if h : pos.byteIdx + pattern.rawEndPos.byteIdx > s.rawEndPos.byteIdx then
        acc ++ accStop.extract s s.rawEndPos
      else
        have := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hPatt _) (Nat.ge_of_not_lt h)
        if Pos.Raw.substrEq s pos pattern 0 pattern.rawEndPos.byteIdx then
          have := Nat.sub_lt_sub_left this (Nat.add_lt_add_left hPatt _)
          loop (acc ++ accStop.extract s pos ++ replacement) (pos + pattern) (pos + pattern)
        else
          have := Nat.sub_lt_sub_left this (Pos.Raw.lt_next s pos)
          loop acc accStop (pos.next s)
      termination_by s.rawEndPos.1 - pos.1
    loop "" 0 0

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
