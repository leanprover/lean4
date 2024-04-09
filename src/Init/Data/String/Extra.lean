/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.ByteArray

namespace String

/-- Interpret the string as the decimal representation of a natural number.

Panics if the string is not a string of digits. -/
def toNat! (s : String) : Nat :=
  if s.isNat then
    s.foldl (fun n c => n*10 + (c.toNat - '0'.toNat)) 0
  else
    panic! "Nat expected"

/--
  Convert a [UTF-8](https://en.wikipedia.org/wiki/UTF-8) encoded `ByteArray` string to `String`.
  The result is unspecified if `a` is not properly UTF-8 encoded.
-/
@[extern "lean_string_from_utf8_unchecked"]
opaque fromUTF8Unchecked (a : @& ByteArray) : String

/-- Convert the given `String` to a [UTF-8](https://en.wikipedia.org/wiki/UTF-8) encoded byte array. -/
@[extern "lean_string_to_utf8"]
opaque toUTF8 (a : @& String) : ByteArray

/-- Accesses a byte in the UTF-8 encoding of the `String`. O(1) -/
@[extern "lean_string_get_byte_fast"]
opaque getUtf8Byte (s : @& String) (n : Nat) (h : n < s.utf8ByteSize) : UInt8

theorem Iterator.sizeOf_next_lt_of_hasNext (i : String.Iterator) (h : i.hasNext) : sizeOf i.next < sizeOf i := by
  cases i; rename_i s pos; simp [Iterator.next, Iterator.sizeOf_eq]; simp [Iterator.hasNext] at h
  exact Nat.sub_lt_sub_left h (String.lt_next s pos)

macro_rules | `(tactic| decreasing_trivial) => `(tactic| apply String.Iterator.sizeOf_next_lt_of_hasNext; assumption)

theorem Iterator.sizeOf_next_lt_of_atEnd (i : String.Iterator) (h : ¬ i.atEnd = true) : sizeOf i.next < sizeOf i :=
  have h : i.hasNext := decide_eq_true <| Nat.gt_of_not_le <| mt decide_eq_true h
  sizeOf_next_lt_of_hasNext i h

macro_rules | `(tactic| decreasing_trivial) => `(tactic| apply String.Iterator.sizeOf_next_lt_of_atEnd; assumption)

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

end String
