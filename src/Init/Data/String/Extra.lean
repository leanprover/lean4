/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
module

prelude
import all Init.Data.ByteArray.Basic
public import Init.Data.String.Basic
import all Init.Data.String.Basic
public import Init.Data.String.Iterator
import all Init.Data.String.Iterator
public import Init.Data.String.Substring
public import Init.Data.String.Modify

public section

namespace Substring

/--
Returns an iterator into the underlying string, at the substring's starting position. The ending
position is discarded, so the iterator alone cannot be used to determine whether its current
position is within the original substring.
-/
@[inline] def toIterator : Substring → String.Iterator
  | ⟨s, b, _⟩ => ⟨s, b⟩

end Substring

namespace String

/--
Interprets a string as the decimal representation of a natural number, returning it. Panics if the
string does not contain a decimal natural number.

A string can be interpreted as a decimal natural number if it is not empty and all the characters in
it are digits.

Use `String.isNat` to check whether `String.toNat!` would return a value. `String.toNat?` is a safer
alternative that returns `none` instead of panicking when the string is not a natural number.

Examples:
 * `"0".toNat! = 0`
 * `"5".toNat! = 5`
 * `"587".toNat! = 587`
-/
def toNat! (s : String) : Nat :=
  if s.isNat then
    s.foldl (fun n c => n*10 + (c.toNat - '0'.toNat)) 0
  else
    panic! "Nat expected"

@[deprecated ByteArray.utf8DecodeChar? (since := "2025-10-01")]
abbrev utf8DecodeChar? (a : ByteArray) (i : Nat) : Option Char :=
  a.utf8DecodeChar? i

/--
Checks whether an array of bytes is a valid UTF-8 encoding of a string.
-/
@[deprecated ByteArray.validateUTF8 (since := "2025-10-01")]
abbrev validateUTF8 (a : ByteArray) : Bool :=
  a.validateUTF8

theorem Iterator.sizeOf_next_lt_of_hasNext (i : String.Iterator) (h : i.hasNext) : sizeOf i.next < sizeOf i := by
  cases i; rename_i s pos; simp [Iterator.next, Iterator.sizeOf_eq]; simp [Iterator.hasNext] at h
  exact Nat.sub_lt_sub_left h (String.Pos.Raw.lt_next s pos)

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

/--
Replaces the current character in the string.

Does nothing if the iterator is at the end of the string. If both the replacement character and the
replaced character are 7-bit ASCII characters and the string is not shared, then it is updated
in-place and not copied.
-/
@[inline] def setCurr : Iterator → Char → Iterator
  | ⟨s, i⟩, c => ⟨i.set s c, i⟩

/--
Moves the iterator forward until the Boolean predicate `p` returns `true` for the iterator's current
character or until the end of the string is reached. Does nothing if the current character already
satisfies `p`.
-/
@[specialize] def find (it : Iterator) (p : Char → Bool) : Iterator :=
  if it.atEnd then it
  else if p it.curr then it
  else find it.next p

/--
Iterates over a string, updating a state at each character using the provided function `f`, until
`f` returns `none`. Begins with the state `init`. Returns the state and character for which `f`
returns `none`.
-/
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

/--
Consistently de-indents the lines in a string, removing the same amount of leading whitespace from
each line such that the least-indented line has no leading whitespace.

The number of leading whitespace characters to remove from each line is determined by counting the
number of leading space (`' '`) and tab (`'\t'`) characters on lines after the first line that also
contain non-whitespace characters. No distinction is made between tab and space characters; both
count equally.

The least number of leading whitespace characters found is then removed from the beginning of each
line. The first line's leading whitespace is not counted when determining how far to de-indent the
string, but leading whitespace is removed from it.

Examples:
* `"Here:\n  fun x =>\n    x + 1".removeLeadingSpaces = "Here:\nfun x =>\n  x + 1"`
* `"Here:\n\t\tfun x =>\n\t  \tx + 1".removeLeadingSpaces = "Here:\nfun x =>\n \tx + 1"`
* `"Here:\n\t\tfun x =>\n \n\t  \tx + 1".removeLeadingSpaces = "Here:\nfun x =>\n\n \tx + 1"`
-/
def removeLeadingSpaces (s : String) : String :=
  let n := findLeadingSpacesSize s
  if n == 0 then s else removeNumLeadingSpaces n s

/--
Replaces each `\r\n` with `\n` to normalize line endings, but does not validate that there are no
isolated `\r` characters.

This is an optimized version of `String.replace text "\r\n" "\n"`.
-/
def crlfToLf (text : String) : String :=
  go "" 0 0
where
  go (acc : String) (accStop pos : String.Pos.Raw) : String :=
    if h : pos.atEnd text then
      -- note: if accStop = 0 then acc is empty
      if accStop = 0 then text else acc ++ accStop.extract text pos
    else
      let c := pos.get' text h
      let pos' := pos.next' text h
      if h' : ¬ pos'.atEnd text ∧ c == '\r' ∧ pos'.get text == '\n' then
        let acc := acc ++ accStop.extract text pos
        go acc pos' (pos'.next' text h'.1)
      else
        go acc accStop pos'
  termination_by text.utf8ByteSize - pos.byteIdx
  decreasing_by
    decreasing_with
      change text.utf8ByteSize - ((pos.next text).next text).byteIdx < text.utf8ByteSize - pos.byteIdx
      have k := Nat.gt_of_not_le <| mt decide_eq_true h
      exact Nat.sub_lt_sub_left k (Nat.lt_trans (String.Pos.Raw.lt_next text pos) (String.Pos.Raw.lt_next _ _))
    decreasing_with
      change text.utf8ByteSize - (pos.next text).byteIdx < text.utf8ByteSize - pos.byteIdx
      have k := Nat.gt_of_not_le <| mt decide_eq_true h
      exact Nat.sub_lt_sub_left k (String.Pos.Raw.lt_next _ _)

end String
