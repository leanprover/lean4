/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Init.Prelude
import Init.While
import Init.Data.String.Basic
import Init.Data.String.Slice.Basic
import Init.Data.String.Length
public import Init.Data.String.Subslice
import Lean.Data.Html.CharRef

namespace Lean.Markdown

/-!
# Text-Level Decoding

Backslash escapes and character references (CommonMark §2.4 and §2.5). The inline parser recognizes
both as inline elements in paragraph text. Link destinations, link titles, and info strings are not
parsed as inlines, so consumers decode them with `decodeText`.
-/

/--
Whether `c` is an ASCII control character (CommonMark §2.1), which is U+0000 to U+001F, or U+007F.
-/
@[inline] public def isAsciiControl (c : Char) : Bool :=
  c.toNat < 0x20 || c.toNat == 0x7F

/--
Whether `c` is in CommonMark's ASCII-punctuation set, which is
``!"#$%&'()*+,-./:;<=>?@[\]^_\`{|}~``. These are the only characters that a backslash escape
consumes; a backslash before any other character is a literal backslash followed by the character.
-/
public def isAsciiPunctuation (c : Char) : Bool :=
  let n := c.toNat
  (33 ≤ n && n ≤ 47) ||  -- ! " # $ % & ' ( ) * + , - . /
  (58 ≤ n && n ≤ 64) ||  -- : ; < = > ? @
  (91 ≤ n && n ≤ 96) ||  -- [ \ ] ^ _ `
  (123 ≤ n && n ≤ 126)   -- { | } ~

/--
Decodes the body of a character reference `&body;` (CommonMark §2.5), which is the text between `&`
and `;`.

Named references are those of HTML. Decimal references (`#` followed by one to seven digits) and
hexadecimal references (`#x` or `#X` followed by one to six hex digits) denote a code point; the
code point zero, surrogates, and values above U+10FFFF decode to U+FFFD.
-/
public def characterReference? {s : String.Slice} (body : s.Subslice) : Option String := do
  let text := body.toSlice
  -- The longest HTML entity name has 31 characters and a numeric body has at most 8, so a longer
  -- body is rejected before it is copied for the lookup. `drop` stops at the end of the text, so
  -- the check costs at most 31 steps.
  guard (text.drop 31).front?.isNone
  let str := body.copy
  if text.front? == some '#' then
    let isHex := (text.drop 1).front? matches some 'x' | some 'X'
    guard (str.length - (if isHex then 2 else 1) ≤ (if isHex then 6 else 7))
    let n ← Html.numericCharacterReference? str
    return String.singleton (Char.ofNat (if n != 0 && n.isValidChar then n else 0xFFFD))
  else
    Html.namedCharacterReference? str

/--
Whether `c` can occur in the body of a character reference. The body consists of ASCII letters,
digits, and `#`.
-/
public def isCharacterReferenceChar (c : Char) : Bool :=
  c.isAlphanum || c == '#'

/--
The largest number of characters that may occur between the `&` and the `;` of a character
reference.

The longest named reference is `CounterClockwiseContourIntegral`, with 31 characters, and a numeric
reference has at most 8, which are `#` and up to 7 decimal digits, or `#x` and up to 6 hexadecimal
digits (CommonMark §2.5).
-/
def maxCharacterReferenceLength : Nat := 31

/--
Parses a character reference whose `&` is immediately before `i`. On success, returns the decoded
text together with the position after the `;`.
-/
public def decodeCharacterReference? {s : String.Slice} (i : s.Pos) : Option (String × s.Pos) :=
    Id.run do
  let mut j := i
  let mut len := 0
  while h : j ≠ s.endPos do
    let c := j.get h
    if c == ';' then
      let body :=
        if hle : i ≤ j then s.subslice i j hle else s.subslice i i (String.Slice.Pos.le_refl i)
      let some value := characterReference? body | return none
      return some (value, j.next h)
    if !isCharacterReferenceChar c || len ≥ maxCharacterReferenceLength then return none
    len := len + 1
    j := j.next h
  return none

/--
Decodes the backslash escapes and character references in `s`. CommonMark applies this decoding to
link destinations, link titles, and the info strings of fenced code blocks.
-/
public def decodeText (text : String) : String := Id.run do
  let s := text.toSlice
  let mut out := ""
  let mut i := s.startPos
  while h : i ≠ s.endPos do
    let c := i.get h
    let j := i.next h
    if c == '\\' then
      if h' : j ≠ s.endPos then
        let d := j.get h'
        if isAsciiPunctuation d then
          out := out.push d
          i := j.next h'
        else
          out := out.push c
          i := j
      else
        out := out.push c
        i := j
    else if c == '&' then
      match decodeCharacterReference? j with
      | some (value, after) =>
        out := out ++ value
        i := after
      | none =>
        out := out.push c
        i := j
    else
      out := out.push c
      i := j
  return out
