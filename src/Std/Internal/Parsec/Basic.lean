/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Dany Fabian, Henrik Böving
-/
prelude
import Init.NotationExtra
import Init.Data.ToString.Macro

namespace Std.Internal

namespace Parsec

inductive ParseResult (α : Type) (ι : Type) where
  | success (pos : ι) (res : α)
  | error (pos : ι) (err : String)
  deriving Repr

end Parsec

def Parsec (ι : Type) (α : Type) : Type := ι → Parsec.ParseResult α ι

namespace Parsec

class Input (ι : Type) (elem : outParam Type) (idx : outParam Type) [DecidableEq idx] [DecidableEq elem] where
  pos : ι → idx
  next : ι → ι
  curr : ι → elem
  hasNext : ι → Bool

variable {α : Type} {ι : Type} {elem : Type} {idx : Type}
variable [DecidableEq idx] [DecidableEq elem] [Input ι elem idx]

instance : Inhabited (Parsec ι α) where
  default := fun it => .error it ""

@[inline]
protected def pure (a : α) : Parsec ι α := fun it =>
  .success it a

@[inline]
def bind {α β : Type} (f : Parsec ι α) (g : α → Parsec ι β) : Parsec ι β := fun it =>
  match f it with
  | .success rem a => g a rem
  | .error pos msg => .error pos msg

instance : Monad (Parsec ι) where
  pure := Parsec.pure
  bind := Parsec.bind

@[inline]
def fail (msg : String) : Parsec ι α := fun it =>
  .error it msg

@[inline]
def tryCatch (p : Parsec ι α) (csuccess : α → Parsec ι β) (cerror : Unit → Parsec ι β)
    : Parsec ι β := fun it =>
  match p it with
  | .success rem a => csuccess a rem
  | .error rem err =>
    -- We assume that it.s never changes as the `Parsec` monad only modifies `it.pos`.
    if Input.pos it = Input.pos rem then cerror () rem else .error rem err

@[inline]
def orElse (p : Parsec ι α) (q : Unit → Parsec ι α) : Parsec ι α :=
  tryCatch p pure q

@[inline]
def attempt (p : Parsec ι α) : Parsec ι α := fun it =>
  match p it with
  | .success rem res => .success rem res
  | .error _ err => .error it err

instance : Alternative (Parsec ι) where
  failure := fail ""
  orElse := orElse

def expectedEndOfInput := "expected end of input"

@[inline]
def eof : Parsec ι Unit := fun it =>
  if Input.hasNext it then
    .error it expectedEndOfInput
  else
    .success it ()

@[inline]
def eof? : Parsec ι Bool := fun it =>
  .success it (!Input.hasNext it)

@[specialize]
partial def manyCore (p : Parsec ι α) (acc : Array α) : Parsec ι <| Array α :=
  tryCatch p (manyCore p <| acc.push ·) (fun _ => pure acc)

@[inline]
def many (p : Parsec ι α) : Parsec ι <| Array α := manyCore p #[]

@[inline]
def many1 (p : Parsec ι α) : Parsec ι <| Array α := do manyCore p #[← p]

def unexpectedEndOfInput := "unexpected end of input"

@[inline]
def any : Parsec ι elem := fun it =>
  if Input.hasNext it then
    .success (Input.next it) (Input.curr it)
  else
    .error it unexpectedEndOfInput

@[inline]
def satisfy (p : elem → Bool) : Parsec ι elem := attempt do
  let c ← any
  if p c then return c else fail "condition not satisfied"

@[inline]
def notFollowedBy (p : Parsec ι α) : Parsec ι Unit := fun it =>
  match p it with
  | .success _ _ => .error it ""
  | .error _ _ => .success it ()

@[inline]
def peek? : Parsec ι (Option elem) := fun it =>
  if Input.hasNext it then
    .success it (Input.curr it)
  else
    .success it none

@[inline]
def peek! : Parsec ι elem := do
  let some c ← peek? | fail unexpectedEndOfInput
  return c

@[inline]
def skip : Parsec ι Unit := fun it =>
  .success (Input.next it) ()

@[specialize]
partial def manyCharsCore (p : Parsec ι Char) (acc : String) : Parsec ι String :=
  tryCatch p (manyCharsCore p <| acc.push ·) (fun _ => pure acc)

@[inline]
def manyChars (p : Parsec ι Char) : Parsec ι String := manyCharsCore p ""

@[inline]
def many1Chars (p : Parsec ι Char) : Parsec ι String := do manyCharsCore p (← p).toString

end Parsec

end Std.Internal
