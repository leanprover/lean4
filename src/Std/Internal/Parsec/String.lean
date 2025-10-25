/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Dany Fabian, Henrik Böving
-/
module

prelude
public import Std.Internal.Parsec.Basic
public import Init.Data.String.Iterator

public section

namespace Std.Internal
namespace Parsec
namespace String

instance : Input String.Iterator Char String.Pos.Raw where
  pos it := it.pos
  next it := it.next
  curr it := it.curr
  hasNext it := it.hasNext
  next' it := it.next'
  curr' it := it.curr'

/--
`Parser α` is a parser that consumes a `String` input using a `String.Iterator` and returns a result of type `α`.
-/
abbrev Parser (α : Type) : Type := Parsec String.Iterator α

/--
Run a `Parser` on a `String`, returns either the result or an error string with offset.
-/
protected def Parser.run (p : Parser α) (s : String) : Except String α :=
  match p s.mkIterator with
  | .success _ res => Except.ok res
  | .error it err => Except.error s!"offset {repr it.pos.byteIdx}: {err}"

/--
Parses the given string.
-/
def pstring (s : String) : Parser String := fun it =>
  let substr := it.extract (it.forward s.length)
  if substr = s then
    .success (it.forward s.length) substr
  else
    .error it (.other s!"expected: {s}")

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
private partial def digitsCore (acc : Nat) : Parser Nat := fun it =>
  /-
  With this design instead of combinators we can avoid allocating and branching over .success values
  all of the time.
  -/
  let ⟨res, it⟩ := go it acc
  .success it res
where
  go (it : String.Iterator) (acc : Nat) : (Nat × String.Iterator) :=
    if h : it.hasNext then
      let candidate := it.curr
      if '0' ≤ candidate ∧ candidate ≤ '9' then
        let digit := digitToNat candidate
        let acc := acc * 10 + digit
        go (it.next' h) acc
      else
        (acc, it)
    else
      (acc, it)

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

private partial def skipWs (it : String.Iterator) : String.Iterator :=
  if h : it.hasNext then
    let c := it.curr' h
    if c = '\u0009' ∨ c = '\u000a' ∨ c = '\u000d' ∨ c = '\u0020' then
      skipWs (it.next' h)
    else
      it
  else
   it

/--
Skip whitespace: tabs, newlines, carriage returns, and spaces.
-/
@[inline]
def ws : Parser Unit := fun it =>
  .success (skipWs it) ()

/--
Takes a fixed amount of chars from the iterator.
-/
def take (n : Nat) : Parser String := fun it =>
  let substr := it.extract (it.forward n)
  if substr.length != n then
    .error it .eof
  else
    .success (it.forward n) substr

end String
end Parsec
end Std.Internal
