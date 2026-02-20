/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Dany Fabian, Henrik Böving
-/
module

prelude
public import Std.Internal.Parsec.Basic
public import Init.Data.String.Slice
public import Init.Data.String.Termination
import Init.Data.Range.Polymorphic

public section

namespace Std.Internal
namespace Parsec
namespace String

instance : Input (Sigma String.Pos) Char String.Pos.Raw where
  pos it := it.2.offset
  next it := ⟨it.1, it.2.next!⟩
  curr it := it.2.get!
  hasNext it := ¬it.2.IsAtEnd
  next' it h := ⟨it.1, it.2.next (by simpa using h)⟩
  curr' it h := it.2.get (by simpa using h)

/--
`Parser α` is a parser that consumes a `String` input using a `Sigma String.Pos` and returns a result of type `α`.
-/
abbrev Parser (α : Type) : Type := Parsec (Sigma String.Pos) α

/--
Run a `Parser` on a `String`, returns either the result or an error string with offset.
-/
protected def Parser.run (p : Parser α) (s : String) : Except String α :=
  match p ⟨s, s.startPos⟩ with
  | .success _ res => Except.ok res
  | .error it err => Except.error s!"offset {repr it.2.offset.byteIdx}: {err}"

/--
Parses the given string.
-/
def pstring (s : String) : Parser String := fun it =>
  match String.Slice.Pattern.ForwardPattern.dropPrefix? s (it.1.sliceFrom it.2) with
  | some p => .success ⟨_, String.Pos.ofSliceFrom p⟩ s
  | none => .error it (.other s!"expected: {s}")

/--
Skips the given string.
-/
@[inline]
def skipString (s : String) : Parser Unit := pstring s *> pure ()

/--
Parses the given char.
-/
@[inline]
def pchar (c : Char) : Parser Char := attempt do
  if (← any) = c then pure c else fail s!"expected: '{c}'"

/--
Skips the given char.
-/
@[inline]
def skipChar (c : Char) : Parser Unit := pchar c *> pure ()

/--
Parse an ASCII digit `0-9` as a `Char`.
-/
@[inline]
def digit : Parser Char := attempt do
  let c ← any
  if '0' ≤ c ∧ c ≤ '9' then return c else fail s!"digit expected"

/--
Convert a byte representing `'0'..'9'` to a `Nat`.
-/
@[inline]
private def digitToNat (b : Char) : Nat := b.toNat - '0'.toNat

@[inline]
private def digitsCore (acc : Nat) : Parser Nat := fun it =>
  /-
  With this design instead of combinators we can avoid allocating and branching over .success values
  all of the time.
  -/
  let ⟨res, it⟩ := go it.2 acc
  .success ⟨_, it⟩ res
where
  go {s : String} (it : s.Pos) (acc : Nat) : (Nat × s.Pos) :=
    if h : ¬it.IsAtEnd then
      let candidate := it.get h
      if '0' ≤ candidate ∧ candidate ≤ '9' then
        let digit := digitToNat candidate
        let acc := acc * 10 + digit
        go (it.next h) acc
      else
        (acc, it)
    else
      (acc, it)
  termination_by it

/--
Parse one or more ASCII digits into a `Nat`.
-/
@[inline]
def digits : Parser Nat := do
  let d ← digit
  digitsCore (digitToNat d)

/--
Parse a hex digit `0-9`, `a-f`, or `A-F` as a `Char`.
-/
@[inline]
def hexDigit : Parser Char := attempt do
  let c ← any
  if ('0' ≤ c ∧ c ≤ '9')
   ∨ ('a' ≤ c ∧ c ≤ 'f')
   ∨ ('A' ≤ c ∧ c ≤ 'F') then return c else fail s!"hex digit expected"

/--
Parse an ASCII letter `a-z` or `A-Z` as a `Char`.
-/
@[inline]
def asciiLetter : Parser Char := attempt do
  let c ← any
  if ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z') then return c else fail s!"ASCII letter expected"

private def skipWs {s : String} (it : s.Pos) : s.Pos :=
  if h : ¬it.IsAtEnd then
    let c := it.get h
    if c = '\u0009' ∨ c = '\u000a' ∨ c = '\u000d' ∨ c = '\u0020' then
      skipWs (it.next h)
    else
      it
  else
   it
termination_by it

/--
Skip whitespace: tabs, newlines, carriage returns, and spaces.
-/
@[inline]
def ws : Parser Unit := fun it =>
  .success ⟨_, skipWs it.2⟩ ()

/--
Takes a fixed amount of chars from the iterator.
-/
def take (n : Nat) : Parser String := fun it => Id.run do
  let mut pos := it.2
  let mut substr := ""
  for _ in 0...n do
    if h : pos.IsAtEnd then
      return .error it .eof
    else
      substr := substr.push (pos.get h)
      pos := pos.next h
  return .success ⟨_, pos⟩ substr

end String
end Parsec
end Std.Internal
