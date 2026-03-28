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
import Init.Data.String.Search
import Init.Data.String.Termination

public section

namespace String

@[deprecated ByteArray.utf8DecodeChar? (since := "2025-10-01")]
abbrev utf8DecodeChar? (a : ByteArray) (i : Nat) : Option Char :=
  a.utf8DecodeChar? i

/--
Checks whether an array of bytes is a valid UTF-8 encoding of a string.
-/
@[deprecated ByteArray.validateUTF8 (since := "2025-10-01")]
abbrev validateUTF8 (a : ByteArray) : Bool :=
  a.validateUTF8

private def findLeadingSpacesSize (s : String) : Nat :=
  let it := s.startPos
  let it := it.find? (· == '\n') |>.bind String.Pos.next?
  match it with
  | some it => consumeSpaces it 0 s.length
  | none => 0
where
  consumeSpaces {s : String} (it : s.Pos) (curr min : Nat) : Nat :=
    if h : it.IsAtEnd then min
    else if it.get h == ' ' || it.get h == '\t' then consumeSpaces (it.next h) (curr + 1) min
    else if it.get h == '\n' then findNextLine (it.next h) min
    else findNextLine (it.next h) (Nat.min curr min)
  termination_by it
  findNextLine {s : String} (it : s.Pos) (min : Nat) : Nat :=
    if h : it.IsAtEnd then min
    else if it.get h == '\n' then consumeSpaces (it.next h) 0 min
    else findNextLine (it.next h) min
  termination_by it

private def removeNumLeadingSpaces (n : Nat) (s : String) : String :=
  consumeSpaces n s.startPos ""
where
  consumeSpaces (n : Nat) {s : String} (it : s.Pos) (r : String) : String :=
     match n with
     | 0 => saveLine it r
     | n+1 =>
       if h : it.IsAtEnd then r
       else if it.get h == ' ' || it.get h == '\t' then consumeSpaces n (it.next h) r
       else saveLine it r
  termination_by (it, 1)
  saveLine {s : String} (it : s.Pos) (r : String) : String :=
    if h : it.IsAtEnd then r
    else if it.get h  == '\n' then consumeSpaces n (it.next h) (r.push '\n')
    else saveLine (it.next h) (r.push (it.get h))
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
