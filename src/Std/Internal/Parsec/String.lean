/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Dany Fabian, Henrik Böving
-/
prelude
import Std.Internal.Parsec.Basic

namespace Std.Internal
namespace Parsec
namespace String

instance : Input String.Iterator Char String.Pos where
  pos it := it.pos
  next it := it.next
  curr it := it.curr
  hasNext it := it.hasNext
  next' it := it.next'
  curr' it := it.curr'

abbrev Parser (α : Type) : Type := Parsec String.Iterator α

protected def Parser.run (p : Parser α) (s : String) : Except String α :=
  match p s.mkIterator with
  | .success _ res => Except.ok res
  | .error it err  => Except.error s!"offset {repr it.i.byteIdx}: {err}"

/-- Parses the given string. -/
def pstring (s : String) : Parser String := fun it =>
  let substr := it.extract (it.forward s.length)
  if substr = s then
    .success (it.forward s.length) substr
  else
    .error it s!"expected: {s}"

@[inline]
def skipString (s : String) : Parser Unit := pstring s *> pure ()

@[inline]
def pchar (c : Char) : Parser Char := attempt do
  if (← any) = c then pure c else fail s!"expected: '{c}'"

@[inline]
def skipChar (c : Char) : Parser Unit := pchar c *> pure ()

@[inline]
def digit : Parser Char := attempt do
  let c ← any
  if '0' ≤ c ∧ c ≤ '9' then return c else fail s!"digit expected"

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

@[inline]
def digits : Parser Nat := do
  let d ← digit
  digitsCore (digitToNat d)

@[inline]
def hexDigit : Parser Char := attempt do
  let c ← any
  if ('0' ≤ c ∧ c ≤ '9')
   ∨ ('a' ≤ c ∧ c ≤ 'f')
   ∨ ('A' ≤ c ∧ c ≤ 'F') then return c else fail s!"hex digit expected"

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

@[inline]
def ws : Parser Unit := fun it =>
  .success (skipWs it) ()

def take (n : Nat) : Parser String := fun it =>
  let substr := it.extract (it.forward n)
  if substr.length != n then
    .error it s!"expected: {n} codepoints"
  else
    .success (it.forward n) substr

end String
end Parsec
end Std.Internal
