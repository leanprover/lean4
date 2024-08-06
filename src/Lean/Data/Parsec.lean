/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Dany Fabian
-/
prelude
import Init.NotationExtra
import Init.Data.ToString.Macro

namespace Lean

namespace Parsec
inductive ParseResult (α : Type) where
  | success (pos : String.Iterator) (res : α)
  | error (pos : String.Iterator) (err : String)
  deriving Repr
end Parsec

def Parsec (α : Type) : Type := String.Iterator → Lean.Parsec.ParseResult α

namespace Parsec

open ParseResult

instance (α : Type) : Inhabited (Parsec α) :=
  ⟨λ it => error it ""⟩

@[always_inline, inline]
protected def pure (a : α) : Parsec α := λ it =>
 success it a

@[always_inline, inline]
def bind {α β : Type} (f : Parsec α) (g : α → Parsec β) : Parsec β := λ it =>
  match f it with
  | success rem a => g a rem
  | error pos msg => error pos msg

@[always_inline]
instance : Monad Parsec :=
  { pure := Parsec.pure, bind }

@[always_inline, inline]
def fail (msg : String) : Parsec α := fun it =>
  error it msg

@[inline]
def tryCatch (p : Parsec α)
    (csuccess : α → Parsec β)
    (cerror : Unit → Parsec β)
    : Parsec β := fun it =>
  match p it with
  | .success rem a => csuccess a rem
  | .error rem err =>
    -- We assume that it.s never changes as the `Parsec` monad only modifies `it.pos`.
    if it.pos = rem.pos then cerror () rem else .error rem err

@[always_inline, inline]
def orElse (p : Parsec α) (q : Unit → Parsec α) : Parsec α :=
  tryCatch p pure q

@[always_inline, inline]
def attempt (p : Parsec α) : Parsec α := λ it =>
  match p it with
  | success rem res => success rem res
  | error _ err => error it err

@[always_inline]
instance : Alternative Parsec :=
  { failure := fail "", orElse }

protected def run (p : Parsec α) (s : String) : Except String α :=
  match p s.mkIterator with
  | Parsec.ParseResult.success _ res => Except.ok res
  | Parsec.ParseResult.error it err  => Except.error s!"offset {repr it.i.byteIdx}: {err}"

def expectedEndOfInput := "expected end of input"

@[inline]
def eof : Parsec Unit := fun it =>
  if it.hasNext then
    error it expectedEndOfInput
  else
    success it ()

@[specialize]
partial def manyCore (p : Parsec α) (acc : Array α) : Parsec $ Array α :=
  tryCatch p (manyCore p <| acc.push ·) (fun _ => pure acc)

@[inline]
def many (p : Parsec α) : Parsec $ Array α := manyCore p #[]

@[inline]
def many1 (p : Parsec α) : Parsec $ Array α := do manyCore p #[←p]

@[specialize]
partial def manyCharsCore (p : Parsec Char) (acc : String) : Parsec String :=
  tryCatch p (manyCharsCore p <| acc.push ·) (fun _ => pure acc)

@[inline]
def manyChars (p : Parsec Char) : Parsec String := manyCharsCore p ""

@[inline]
def many1Chars (p : Parsec Char) : Parsec String := do manyCharsCore p (←p).toString

/-- Parses the given string. -/
def pstring (s : String) : Parsec String := λ it =>
  let substr := it.extract (it.forward s.length)
  if substr = s then
    success (it.forward s.length) substr
  else
    error it s!"expected: {s}"

@[inline]
def skipString (s : String) : Parsec Unit := pstring s *> pure ()

def unexpectedEndOfInput := "unexpected end of input"

@[inline]
def anyChar : Parsec Char := λ it =>
  if h : it.hasNext then
    let c := it.curr' h
    let it' := it.next' h
    success it' c
  else
    error it unexpectedEndOfInput

@[inline]
def pchar (c : Char) : Parsec Char := attempt do
  if (←anyChar) = c then pure c else fail s!"expected: '{c}'"

@[inline]
def skipChar (c : Char) : Parsec Unit := pchar c *> pure ()

@[inline]
def digit : Parsec Char := attempt do
  let c ← anyChar
  if '0' <= c && c <= '9' then return c else fail s!"digit expected"

@[inline]
def hexDigit : Parsec Char := attempt do
  let c ← anyChar
  if ('0' <= c && c <= '9')
   || ('a' <= c && c <= 'f')
   || ('A' <= c && c <= 'F') then return c else fail s!"hex digit expected"

@[inline]
def asciiLetter : Parsec Char := attempt do
  let c ← anyChar
  if ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z') then return c else fail s!"ASCII letter expected"

@[inline]
def satisfy (p : Char → Bool) : Parsec Char := attempt do
  let c ← anyChar
  if p c then return c else fail "condition not satisfied"

@[inline]
def notFollowedBy (p : Parsec α) : Parsec Unit := λ it =>
  match p it with
  | success _ _ => error it ""
  | error _ _ => success it ()

partial def skipWs (it : String.Iterator) : String.Iterator :=
  if h : it.hasNext then
    let c := it.curr' h
    if c == '\u0009' || c == '\u000a' || c == '\u000d' || c == '\u0020' then
      skipWs (it.next' h)
    else
      it
  else
   it

@[inline]
def peek? : Parsec (Option Char) := fun it =>
  -- `String.Iterator.curr'` uses `lean_string_utf8_get_fast`, which has an inlined
  -- fast path for ASCII symbols. This means that using `it.curr'` is significantly
  -- faster than `it.curr` on inputs that are mostly ASCII.
  if h : it.hasNext then
    success it (it.curr' h)
  else
    success it none

@[inline]
def peek! : Parsec Char := fun it =>
  if h : it.hasNext then
    success it (it.curr' h)
  else
    error it unexpectedEndOfInput

@[inline]
def peekD (default : Char) : Parsec Char := fun it =>
  if h : it.hasNext then
    success it (it.curr' h)
  else
    success it default

@[inline]
def skip : Parsec Unit := fun it =>
  if h : it.hasNext then
    success (it.next' h) ()
  else
    error it unexpectedEndOfInput

@[inline]
def ws : Parsec Unit := fun it =>
  success (skipWs it) ()
end Parsec
