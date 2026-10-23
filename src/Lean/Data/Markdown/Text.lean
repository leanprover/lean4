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
import Lean.Data.Html.CharRef

namespace Lean.Markdown

/-!
# Text-level decoding

CommonMark §2.4 and §2.5: backslash escapes and character references. The inline parser recognizes
both as inline elements in paragraph text. Link destinations, link titles, and info strings are not
parsed as inlines, so consumers decode them with `decodeText`.
-/

/--
Whether `c` is in CommonMark's ASCII-punctuation set: ``!"#$%&'()*+,-./:;<=>?@[\]^_\`{|}~``. These
are the only characters that a backslash escape consumes; a backslash before any other character is
a literal backslash followed by the character.
-/
public def isAsciiPunctuation (c : Char) : Bool :=
  let n := c.toNat
  (33 ≤ n && n ≤ 47) ||  -- ! " # $ % & ' ( ) * + , - . /
  (58 ≤ n && n ≤ 64) ||  -- : ; < = > ? @
  (91 ≤ n && n ≤ 96) ||  -- [ \ ] ^ _ `
  (123 ≤ n && n ≤ 126)   -- { | } ~

/--
Decodes the body of a character reference `&body;` (CommonMark §2.5): the text between `&` and `;`.

Named references are those of HTML. Decimal references (`#` followed by one to seven digits) and
hexadecimal references (`#x` or `#X` followed by one to six hex digits) denote a code point; the
code point zero, surrogates, and values above U+10FFFF decode to U+FFFD.
-/
public def characterReference? (body : String) : Option String :=
  match Html.numericCharacterReference? body with
  | some n => do
    -- The body is ASCII, so its byte size is its length. The digits follow `#` or `#x`.
    let second := String.Pos.Raw.get body ⟨1⟩
    let isHex := second == 'x' || second == 'X'
    guard (body.utf8ByteSize - (if isHex then 2 else 1) ≤ (if isHex then 6 else 7))
    return String.singleton (Char.ofNat (if n != 0 && n.isValidChar then n else 0xFFFD))
  | none => Html.namedCharacterReference? body

/--
Whether `c` can occur in the body of a character reference: ASCII letters and digits, and `#`.
-/
public def isCharacterReferenceChar (c : Char) : Bool :=
  c.isAlphanum || c == '#'

/--
Parses a character reference whose `&` is immediately before `i`. On success, returns the decoded
text together with the position after the `;`.
-/
public def decodeCharacterReference? (s : String) (i : String.Pos.Raw) :
    Option (String × String.Pos.Raw) := Id.run do
  let mut j := i
  while h : ¬ j.atEnd s do
    let c := j.get' s h
    if c == ';' then
      let some value := characterReference? (i.extract s j) | return none
      return some (value, j.next' s h)
    if !isCharacterReferenceChar c then return none
    j := j.next' s h
  return none

/--
Decodes the backslash escapes and character references in `s`. CommonMark applies this decoding to
link destinations, link titles, and the info strings of fenced code blocks.
-/
public def decodeText (s : String) : String := Id.run do
  let mut out := ""
  let mut i : String.Pos.Raw := 0
  while h : ¬ i.atEnd s do
    let c := i.get' s h
    let j := i.next' s h
    if c == '\\' then
      if h' : ¬ j.atEnd s then
        let d := j.get' s h'
        if isAsciiPunctuation d then
          out := out.push d
          i := j.next' s h'
        else
          out := out.push c
          i := j
      else
        out := out.push c
        i := j
    else if c == '&' then
      match decodeCharacterReference? s j with
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
