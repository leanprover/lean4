/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Dany Fabian, Henrik Böving
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

instance (α : Type) : Inhabited (Parsec α) where
  default := fun it => error it ""

@[inline]
protected def pure (a : α) : Parsec α := fun it =>
  success it a

@[inline]
def bind {α β : Type} (f : Parsec α) (g : α → Parsec β) : Parsec β := fun it =>
  match f it with
  | success rem a => g a rem
  | error pos msg => error pos msg

instance : Monad Parsec where
  pure := Parsec.pure
  bind := Parsec.bind

@[inline]
def fail (msg : String) : Parsec α := fun it =>
  error it msg

@[inline]
def tryCatch (p : Parsec α) (csuccess : α → Parsec β) (cerror : Unit → Parsec β)
    : Parsec β := fun it =>
  match p it with
  | .success rem a => csuccess a rem
  | .error rem err =>
    -- We assume that it.s never changes as the `Parsec` monad only modifies `it.pos`.
    if it.pos = rem.pos then cerror () rem else .error rem err

@[inline]
def orElse (p : Parsec α) (q : Unit → Parsec α) : Parsec α :=
  tryCatch p pure q

@[inline]
def attempt (p : Parsec α) : Parsec α := λ it =>
  match p it with
  | success rem res => success rem res
  | error _ err => error it err

instance : Alternative Parsec where
  failure := fail ""
  orElse := orElse

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
def many (p : Parsec α) : Parsec <| Array α := manyCore p #[]

@[inline]
def many1 (p : Parsec α) : Parsec <| Array α := do manyCore p #[← p]

def unexpectedEndOfInput := "unexpected end of input"

@[inline]
def anyChar : Parsec Char := fun it =>
  if it.hasNext then success it.next it.curr else error it unexpectedEndOfInput

@[inline]
def satisfy (p : Char → Bool) : Parsec Char := attempt do
  let c ← anyChar
  if p c then return c else fail "condition not satisfied"

@[inline]
def notFollowedBy (p : Parsec α) : Parsec Unit := fun it =>
  match p it with
  | success _ _ => error it ""
  | error _ _ => success it ()

@[inline]
def peek? : Parsec (Option Char) := fun it =>
  if it.hasNext then
    success it it.curr
  else
    success it none

@[inline]
def peek! : Parsec Char := do
  let some c ← peek? | fail unexpectedEndOfInput
  return c

@[inline]
def skip : Parsec Unit := fun it =>
  success it.next ()

@[specialize]
partial def manyCharsCore (p : Parsec ι Char) (acc : String) : Parsec ι String :=
  tryCatch p (manyCharsCore p <| acc.push ·) (fun _ => pure acc)

@[inline]
def manyChars (p : Parsec ι Char) : Parsec ι String := manyCharsCore p ""

@[inline]
def many1Chars (p : Parsec ι Char) : Parsec ι String := do manyCharsCore p (← p).toString


end Parsec
