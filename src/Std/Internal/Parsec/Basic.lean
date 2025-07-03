/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Dany Fabian, Henrik Böving, Sofia Rodrigues
-/
module

prelude
public import Init.NotationExtra
public import Init.Data.ToString.Macro

public section

namespace Std
namespace Internal
namespace Parsec

/--
Error type for the `ParseResult`. It separates `eof` from the rest of the errors in order to
improve the error handling for this case in parsers that can receive incomplete data and then reparse it.
-/
inductive Error where
  | eof
  | other (s : String)
  deriving Repr

instance : ToString Error where
  toString
    | .eof => "unexpected end of input"
    | .other s => s

/--
The result of parsing some string.
-/
inductive ParseResult (α : Type) (ι : Type) where
  | success (pos : ι) (res : α)
  | error (pos : ι) (err : Error)
  deriving Repr

end Parsec

@[expose]
def Parsec (ι : Type) (α : Type) : Type :=
  ι → Parsec.ParseResult α ι

namespace Parsec

class Input (ι : Type) (elem : outParam Type) (idx : outParam Type) [DecidableEq idx] [DecidableEq elem] where
  pos : ι → idx
  next : ι → ι
  curr : ι → elem
  hasNext : ι → Bool
  next' (it : ι) : (hasNext it) → ι
  curr' (it : ι) : (hasNext it) → elem

variable {α : Type} {ι : Type} {elem : Type} {idx : Type}
variable [DecidableEq idx] [DecidableEq elem] [Input ι elem idx]

instance : Inhabited (Parsec ι α) where
  default := fun it => ParseResult.error it (.other "")

@[always_inline, inline]
protected def pure (a : α) : Parsec ι α := fun it =>
  .success it a

@[always_inline, inline]
protected def bind {α β : Type} (f : Parsec ι α) (g : α → Parsec ι β) : Parsec ι β := fun it =>
  match f it with
  | .success rem a => g a rem
  | .error pos msg => .error pos msg

@[always_inline, inline]
def fail (msg : String) : Parsec ι α := fun it =>
  .error it (.other msg)

@[inline]
def tryCatch (p : Parsec ι α) (csuccess : α → Parsec ι β) (cerror : Unit → Parsec ι β)
    : Parsec ι β := fun it =>
  match p it with
  | .success rem a => csuccess a rem
  | .error rem err =>
    -- We assume that it.s never changes as the `Parsec` monad only modifies `it.pos`.
    if Input.pos it = Input.pos rem then cerror () rem else .error rem err

@[always_inline]
instance : Monad (Parsec ι) where
  pure := Parsec.pure
  bind := Parsec.bind

@[always_inline, inline]
def orElse (p : Parsec ι α) (q : Unit → Parsec ι α) : Parsec ι α :=
  tryCatch p pure q

@[always_inline, inline]
def attempt (p : Parsec ι α) : Parsec ι α := fun it =>
  match p it with
  | .success rem res => .success rem res
  | .error _ err => .error it err

@[always_inline]
instance : Alternative (Parsec ι) where
  failure := fail ""
  orElse := orElse

@[inline]
def eof : Parsec ι Unit := fun it =>
  if Input.hasNext it then
    .error it .eof
  else
    .success it ()

@[inline]
def isEof : Parsec ι Bool := fun it =>
  .success it (!Input.hasNext it)

@[specialize]
partial def manyCore (p : Parsec ι α) (acc : Array α) : Parsec ι <| Array α :=
  tryCatch p (manyCore p <| acc.push ·) (fun _ => pure acc)

@[inline]
def many (p : Parsec ι α) : Parsec ι <| Array α := manyCore p #[]

@[inline]
def many1 (p : Parsec ι α) : Parsec ι <| Array α := do manyCore p #[← p]

/--
Gets the next input element.
-/
@[inline]
def any : Parsec ι elem := fun it =>
  if h : Input.hasNext it then
    let c := Input.curr' it h
    let it' := Input.next' it h
    .success it' c
  else
    .error it .eof

/--
Checks if the next input element matches some condition.
-/
@[inline]
def satisfy (p : elem → Bool) : Parsec ι elem := attempt do
  let c ← any
  if p c then return c else fail "condition not satisfied"

/--
Fails if `p` succeeds, otherwise succeeds without consuming input.
-/
@[inline]
def notFollowedBy (p : Parsec ι α) : Parsec ι Unit := fun it =>
  match p it with
  | .success _ _ => .error it (.other "")
  | .error _ _ => .success it ()

/--
Peeks at the next element, returns `some` if exists else `none`, does not consume input.
-/
@[inline]
def peek? : Parsec ι (Option elem) := fun it =>
  if h : Input.hasNext it then
    .success it (some <| Input.curr' it h)
  else
    .success it none

/--
Peeks at the next element, returns `some elem` if it satisfies `p`, else `none`. Does not consume input.
-/
@[inline]
def peekWhen? (p : elem → Bool) : Parsec ι (Option elem) := do
  let some data ← peek?
    | return none

  if p data then
    return some data
  else
    return none

/--
Peeks at the next element, errors on EOF, does not consume input.
-/
@[inline]
def peek! : Parsec ι elem := fun it =>
  if h : Input.hasNext it then
    .success it (Input.curr' it h)
  else
    .error it .eof

/--
Peeks at the next element or returns a default if at EOF, does not consume input.
-/
@[inline]
def peekD (default : elem) : Parsec ι elem := fun it =>
  if h : Input.hasNext it then
    .success it (Input.curr' it h)
  else
    .success it default

/--
Consumes one element if available, otherwise errors on EOF.
-/
@[inline]
def skip : Parsec ι Unit := fun it =>
  if h : Input.hasNext it then
    .success (Input.next' it h) ()
  else
    .error it .eof

/--
Parses zero or more chars with `p`, accumulates into a string.
-/
@[specialize]
partial def manyCharsCore (p : Parsec ι Char) (acc : String) : Parsec ι String :=
  tryCatch p (manyCharsCore p <| acc.push ·) (fun _ => pure acc)

/--
Parses zero or more chars with `p` into a string.
-/
@[inline]
def manyChars (p : Parsec ι Char) : Parsec ι String := do
  manyCharsCore p ""

/--
Parses one or more chars with `p` into a string, errors if none.
-/
@[inline]
def many1Chars (p : Parsec ι Char) : Parsec ι String := do
  manyCharsCore p (← p).toString

end Parsec
end Internal
end Std
