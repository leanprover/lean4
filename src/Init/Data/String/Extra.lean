/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.ByteArray
import Init.Data.UInt.Lemmas

namespace String

/-- Interpret the string as the decimal representation of a natural number.

Panics if the string is not a string of digits. -/
def toNat! (s : String) : Nat :=
  if s.isNat then
    s.foldl (fun n c => n*10 + (c.toNat - '0'.toNat)) 0
  else
    panic! "Nat expected"

def utf8DecodeChar? (a : ByteArray) (i : Nat) : Option Char := do
  let c ← a[i]?
  if c &&& 0x80 == 0 then
    some ⟨c.toUInt32, .inl (Nat.lt_trans c.toBitVec.isLt (by decide))⟩
  else if c &&& 0xe0 == 0xc0 then
    let c1 ← a[i+1]?
    guard (c1 &&& 0xc0 == 0x80)
    let r := ((c &&& 0x1f).toUInt32 <<< 6) ||| (c1 &&& 0x3f).toUInt32
    guard (0x80 ≤ r)
    -- TODO: Prove h from the definition of r once we have the necessary lemmas
    if h : r < 0xd800 then some ⟨r, .inl (UInt32.toNat_lt_of_lt (by decide) h)⟩ else none
  else if c &&& 0xf0 == 0xe0 then
    let c1 ← a[i+1]?
    let c2 ← a[i+2]?
    guard (c1 &&& 0xc0 == 0x80 && c2 &&& 0xc0 == 0x80)
    let r :=
      ((c &&& 0x0f).toUInt32 <<< 12) |||
      ((c1 &&& 0x3f).toUInt32 <<< 6) |||
      (c2 &&& 0x3f).toUInt32
    guard (0x800 ≤ r)
    -- TODO: Prove `r < 0x110000` from the definition of r once we have the necessary lemmas
    if h : r < 0xd800 ∨ 0xdfff < r ∧ r < 0x110000 then
      have :=
        match h with
        | .inl h => Or.inl (UInt32.toNat_lt_of_lt (by decide) h)
        | .inr h => Or.inr ⟨UInt32.lt_toNat_of_lt (by decide) h.left, UInt32.toNat_lt_of_lt (by decide) h.right⟩
      some ⟨r, this⟩
    else
      none
  else if c &&& 0xf8 == 0xf0 then
    let c1 ← a[i+1]?
    let c2 ← a[i+2]?
    let c3 ← a[i+3]?
    guard (c1 &&& 0xc0 == 0x80 && c2 &&& 0xc0 == 0x80 && c3 &&& 0xc0 == 0x80)
    let r :=
      ((c &&& 0x07).toUInt32 <<< 18) |||
      ((c1 &&& 0x3f).toUInt32 <<< 12) |||
      ((c2 &&& 0x3f).toUInt32 <<< 6) |||
      (c3 &&& 0x3f).toUInt32
    if h : 0x10000 ≤ r ∧ r < 0x110000 then
      some ⟨r, .inr ⟨Nat.lt_of_lt_of_le (by decide) (UInt32.le_toNat_of_le (by decide) h.left), UInt32.toNat_lt_of_lt (by decide) h.right⟩⟩
    else none
  else
    none

/-- Returns true if the given byte array consists of valid UTF-8. -/
@[extern "lean_string_validate_utf8"]
def validateUTF8 (a : @& ByteArray) : Bool :=
  (loop 0).isSome
where
  loop (i : Nat) : Option Unit := do
    if i < a.size then
      let c ← utf8DecodeChar? a i
      loop (i + c.utf8Size)
    else pure ()
  termination_by a.size - i
  decreasing_by exact Nat.sub_lt_sub_left ‹_› (Nat.lt_add_of_pos_right c.utf8Size_pos)

/-- Converts a [UTF-8](https://en.wikipedia.org/wiki/UTF-8) encoded `ByteArray` string to `String`. -/
@[extern "lean_string_from_utf8_unchecked"]
def fromUTF8 (a : @& ByteArray) (h : validateUTF8 a) : String :=
  loop 0 ""
where
  loop (i : Nat) (acc : String) : String :=
    if i < a.size then
      let c := (utf8DecodeChar? a i).getD default
      loop (i + c.utf8Size) (acc.push c)
    else acc
  termination_by a.size - i
  decreasing_by exact Nat.sub_lt_sub_left ‹_› (Nat.lt_add_of_pos_right c.utf8Size_pos)

/-- Converts a [UTF-8](https://en.wikipedia.org/wiki/UTF-8) encoded `ByteArray` string to `String`,
or returns `none` if `a` is not properly UTF-8 encoded. -/
@[inline] def fromUTF8? (a : ByteArray) : Option String :=
  if h : validateUTF8 a then fromUTF8 a h else none

/-- Converts a [UTF-8](https://en.wikipedia.org/wiki/UTF-8) encoded `ByteArray` string to `String`,
or panics if `a` is not properly UTF-8 encoded. -/
@[inline] def fromUTF8! (a : ByteArray) : String :=
  if h : validateUTF8 a then fromUTF8 a h else panic! "invalid UTF-8 string"

def utf8EncodeChar (c : Char) : List UInt8 :=
  let v := c.val
  if v ≤ 0x7f then
    [v.toUInt8]
  else if v ≤ 0x7ff then
    [(v >>>  6).toUInt8 &&& 0x1f ||| 0xc0,
              v.toUInt8 &&& 0x3f ||| 0x80]
  else if v ≤ 0xffff then
    [(v >>> 12).toUInt8 &&& 0x0f ||| 0xe0,
     (v >>>  6).toUInt8 &&& 0x3f ||| 0x80,
              v.toUInt8 &&& 0x3f ||| 0x80]
  else
    [(v >>> 18).toUInt8 &&& 0x07 ||| 0xf0,
     (v >>> 12).toUInt8 &&& 0x3f ||| 0x80,
     (v >>>  6).toUInt8 &&& 0x3f ||| 0x80,
              v.toUInt8 &&& 0x3f ||| 0x80]

@[simp] theorem length_utf8EncodeChar (c : Char) : (utf8EncodeChar c).length = c.utf8Size := by
  simp [Char.utf8Size, utf8EncodeChar]
  cases Decidable.em (c.val ≤ 0x7f) <;> simp [*]
  cases Decidable.em (c.val ≤ 0x7ff) <;> simp [*]
  cases Decidable.em (c.val ≤ 0xffff) <;> simp [*]

/-- Converts the given `String` to a [UTF-8](https://en.wikipedia.org/wiki/UTF-8) encoded byte array. -/
@[extern "lean_string_to_utf8"]
def toUTF8 (a : @& String) : ByteArray :=
  ⟨⟨a.data.flatMap utf8EncodeChar⟩⟩

@[simp] theorem size_toUTF8 (s : String) : s.toUTF8.size = s.utf8ByteSize := by
  simp [toUTF8, ByteArray.size, Array.size, utf8ByteSize, List.flatMap]
  induction s.data <;> simp [List.map, List.flatten, utf8ByteSize.go, Nat.add_comm, *]

/-- Accesses a byte in the UTF-8 encoding of the `String`. O(1) -/
@[extern "lean_string_get_byte_fast"]
def getUtf8Byte (s : @& String) (n : Nat) (h : n < s.utf8ByteSize) : UInt8 :=
  (toUTF8 s)[n]'(size_toUTF8 _ ▸ h)

theorem Iterator.sizeOf_next_lt_of_hasNext (i : String.Iterator) (h : i.hasNext) : sizeOf i.next < sizeOf i := by
  cases i; rename_i s pos; simp [Iterator.next, Iterator.sizeOf_eq]; simp [Iterator.hasNext] at h
  exact Nat.sub_lt_sub_left h (String.lt_next s pos)

macro_rules
| `(tactic| decreasing_trivial) =>
  `(tactic| with_reducible apply String.Iterator.sizeOf_next_lt_of_hasNext; assumption)

theorem Iterator.sizeOf_next_lt_of_atEnd (i : String.Iterator) (h : ¬ i.atEnd = true) : sizeOf i.next < sizeOf i :=
  have h : i.hasNext := decide_eq_true <| Nat.gt_of_not_le <| mt decide_eq_true h
  sizeOf_next_lt_of_hasNext i h

macro_rules
| `(tactic| decreasing_trivial) =>
  `(tactic| with_reducible apply String.Iterator.sizeOf_next_lt_of_atEnd; assumption)

namespace Iterator

/-- Advance the given iterator until the predicate returns true or the end of the string is reached. -/
@[specialize] def find (it : Iterator) (p : Char → Bool) : Iterator :=
  if it.atEnd then it
  else if p it.curr then it
  else find it.next p

@[specialize] def foldUntil (it : Iterator) (init : α) (f : α → Char → Option α) : α × Iterator :=
  if it.atEnd then
    (init, it)
  else if let some a := f init it.curr then
    foldUntil it.next a f
  else
    (init, it)

end Iterator

private def findLeadingSpacesSize (s : String) : Nat :=
  let it := s.iter
  let it := it.find (· == '\n') |>.next
  consumeSpaces it 0 s.length
where
  consumeSpaces (it : String.Iterator) (curr min : Nat) : Nat :=
    if it.atEnd then min
    else if it.curr == ' ' || it.curr == '\t' then consumeSpaces it.next (curr + 1) min
    else if it.curr == '\n' then findNextLine it.next min
    else findNextLine it.next (Nat.min curr min)
  findNextLine (it : String.Iterator) (min : Nat) : Nat :=
    if it.atEnd then min
    else if it.curr == '\n' then consumeSpaces it.next 0 min
    else findNextLine it.next min

private def removeNumLeadingSpaces (n : Nat) (s : String) : String :=
  consumeSpaces n s.iter ""
where
  consumeSpaces (n : Nat) (it : String.Iterator) (r : String) : String :=
     match n with
     | 0 => saveLine it r
     | n+1 =>
       if it.atEnd then r
       else if it.curr == ' ' || it.curr == '\t' then consumeSpaces n it.next r
       else saveLine it r
  termination_by (it, 1)
  saveLine (it : String.Iterator) (r : String) : String :=
    if it.atEnd then r
    else if it.curr == '\n' then consumeSpaces n it.next (r.push '\n')
    else saveLine it.next (r.push it.curr)
  termination_by (it, 0)

def removeLeadingSpaces (s : String) : String :=
  let n := findLeadingSpacesSize s
  if n == 0 then s else removeNumLeadingSpaces n s

/--
Replaces each `\r\n` with `\n` to normalize line endings,
but does not validate that there are no isolated `\r` characters.
It is an optimized version of `String.replace text "\r\n" "\n"`.
-/
def crlfToLf (text : String) : String :=
  go "" 0 0
where
  go (acc : String) (accStop pos : String.Pos) : String :=
    if h : text.atEnd pos then
      -- note: if accStop = 0 then acc is empty
      if accStop = 0 then text else acc ++ text.extract accStop pos
    else
      let c := text.get' pos h
      let pos' := text.next' pos h
      if h' : ¬ text.atEnd pos' ∧ c == '\r' ∧ text.get pos' == '\n' then
        let acc := acc ++ text.extract accStop pos
        go acc pos' (text.next' pos' h'.1)
      else
        go acc accStop pos'
  termination_by text.utf8ByteSize - pos.byteIdx
  decreasing_by
    decreasing_with
      show text.utf8ByteSize - (text.next (text.next pos)).byteIdx < text.utf8ByteSize - pos.byteIdx
      have k := Nat.gt_of_not_le <| mt decide_eq_true h
      exact Nat.sub_lt_sub_left k (Nat.lt_trans (String.lt_next text pos) (String.lt_next _ _))
    decreasing_with
      show text.utf8ByteSize - (text.next pos).byteIdx < text.utf8ByteSize - pos.byteIdx
      have k := Nat.gt_of_not_le <| mt decide_eq_true h
      exact Nat.sub_lt_sub_left k (String.lt_next _ _)

end String
