/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Marc Huisinga
-/
import Lean.Data.Json.Basic

namespace Lean

open Std (RBNode RBNode.singleton RBNode.leaf)

inductive Quickparse.Result (α : Type) where
  | success (pos : String.Iterator) (res : α)    : Result α
  | error (pos : String.Iterator) (err : String) : Result α

def Quickparse (α : Type) : Type := String.Iterator → Lean.Quickparse.Result α

instance (α : Type) : Inhabited (Quickparse α) :=
  ⟨fun it => Quickparse.Result.error it ""⟩

namespace Quickparse

open Result

partial def skipWs (it : String.Iterator) : String.Iterator :=
  if it.hasNext then
    let c := it.curr
    if c = '\u0009' ∨ c = '\u000a' ∨ c = '\u000d' ∨ c = '\u0020' then
      skipWs it.next
    else
      it
  else
   it

@[inline]
protected def pure (a : α) : Quickparse α := fun it =>
  success it a

@[inline]
protected def bind {α β : Type} (f : Quickparse α) (g : α → Quickparse β) : Quickparse β := fun it =>
  match f it with
  | success rem a => g a rem
  | error pos msg => error pos msg

@[inline]
def fail (msg : String) : Quickparse α := fun it =>
  error it msg

@[inline]
instance : Monad Quickparse :=
  { pure := @Quickparse.pure, bind := @Quickparse.bind }

def unexpectedEndOfInput := "unexpected end of input"

@[inline]
def peek? : Quickparse (Option Char) := fun it =>
  if it.hasNext then
    success it it.curr
  else
    success it none

@[inline]
def peek! : Quickparse Char := do
  let some c ← peek? | fail unexpectedEndOfInput
  c

@[inline]
def skip : Quickparse Unit := fun it =>
  success it.next ()

@[inline]
def next : Quickparse Char := do
  let c ← peek!
  skip
  c

def expect (s : String) : Quickparse Unit := fun it =>
  if it.extract (it.forward s.length) = s then
    success (it.forward s.length) ()
  else
    error it s!"expected: {s}"

@[inline]
def ws : Quickparse Unit := fun it =>
  success (skipWs it) ()

def expectedEndOfInput := "expected end of input"

@[inline]
def eoi : Quickparse Unit := fun it =>
  if it.hasNext then
    error it expectedEndOfInput
  else
    success it ()

end Quickparse

namespace Json.Parser

open Quickparse

@[inline]
def hexChar : Quickparse Nat := do
  let c ← next
  if '0' ≤ c ∧ c ≤ '9' then
    pure $ c.val.toNat - '0'.val.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then
    pure $ c.val.toNat - 'a'.val.toNat
  else if 'A' ≤ c ∧ c ≤ 'F' then
    pure $ c.val.toNat - 'A'.val.toNat
  else
    fail "invalid hex character"

def escapedChar : Quickparse Char := do
  let c ← next
  match c with
  | '\\' => '\\'
  | '"'  => '"'
  | '/'  => '/'
  | 'b'  => '\x08'
  | 'f'  => '\x0c'
  | 'n'  => '\n'
  | 'r'  => '\x0d'
  | 't'  => '\t'
  | 'u'  =>
    let u1 ← hexChar; let u2 ← hexChar; let u3 ← hexChar; let u4 ← hexChar
    Char.ofNat $ 4096*u1 + 256*u2 + 16*u3 + u4
  | _ => fail "illegal \\u escape"

partial def strCore (acc : String) : Quickparse String := do
  let c ← peek!
  if c = '"' then -- "
    skip
    acc
  else
    let c ← next
    let ec ←
      if c = '\\' then
        escapedChar
      -- as to whether c.val > 0xffff should be split up and encoded with multiple \u,
      -- the JSON standard is not definite: both directly printing the character
      -- and encoding it with multiple \u is allowed. we choose the former.
      else if 0x0020 ≤ c.val ∧ c.val ≤ 0x10ffff then
        c
      else
        fail "unexpected character in string"
    strCore (acc.push ec)

def str : Quickparse String := strCore ""

partial def natCore (acc digits : Nat) : Quickparse (Nat × Nat) := do
  let some c ← peek? | (acc, digits)
  if '0' ≤ c ∧ c ≤ '9' then
    skip
    let acc' := 10*acc + (c.val.toNat - '0'.val.toNat)
    natCore acc' (digits+1)
  else
    (acc, digits)

@[inline]
def lookahead (p : Char → Prop) (desc : String) [DecidablePred p] : Quickparse Unit := do
  let c ← peek!
  if p c then
    ()
  else
    fail $ "expected " ++ desc

@[inline]
def natNonZero : Quickparse Nat := do
  lookahead (fun c => '1' ≤ c ∧ c ≤ '9') "1-9"
  let (n, _) ← natCore 0 0
  n

@[inline]
def natNumDigits : Quickparse (Nat × Nat) := do
  lookahead (fun c => '0' ≤ c ∧ c ≤ '9') "digit"
  natCore 0 0

@[inline]
def natMaybeZero : Quickparse Nat := do
  let (n, _) ← natNumDigits
  n

def num : Quickparse JsonNumber := do
  let c ← peek!
  let sign : Int ←
    if c = '-' then
      skip
      pure (-1 : Int)
    else
      pure 1
  let c ← peek!
  let res ←
    if c = '0' then
      skip
      pure 0
    else
      natNonZero
  let c? ← peek?
  let res : JsonNumber ←
    if c? = some '.' then
      skip
      let (n, d) ← natNumDigits
      if d > USize.size then fail "too many decimals"
      let mantissa' := sign * (res * (10^d : Nat) + n)
      let exponent' := d
      JsonNumber.mk mantissa' exponent'
    else
      JsonNumber.fromInt (sign * res)
  let c? ← peek?
  if c? = some 'e' ∨ c? = some 'E' then
    skip
    let c ← peek!
    if c = '-' then
      skip
      let n ← natMaybeZero
      res.shiftr n
    else
      if c = '+' then skip
      let n ← natMaybeZero
      if n > USize.size then fail "exp too large"
      res.shiftl n
  else
    res

partial def arrayCore (anyCore : Unit → Quickparse Json) (acc : Array Json) : Quickparse (Array Json) := do
  let hd ← anyCore ()
  let acc' := acc.push hd
  let c ← next
  if c = ']' then
    ws
    acc'
  else if c = ',' then
    ws
    arrayCore anyCore acc'
  else
    fail "unexpected character in array"

partial def objectCore (anyCore : Unit → Quickparse Json) : Quickparse (RBNode String (fun _ => Json)) := do
  lookahead (fun c => c = '"') "\""; skip; -- "
  let k ← strCore ""; ws
  lookahead (fun c => c = ':') ":"; skip; ws
  let v ← anyCore ()
  let c ← next
  if c = '}' then
    ws
    RBNode.singleton k v
  else if c = ',' then
    ws
    let kvs ← objectCore anyCore
    kvs.insert strLt k v
  else
    fail "unexpected character in object"

-- takes a unit parameter so that
-- we can use the equation compiler and recursion
partial def anyCore (u : Unit) : Quickparse Json := do
  let c ← peek!
  if c = '[' then
    skip; ws
    let c ← peek!
    if c = ']' then
      skip; ws
      Json.arr (Array.mkEmpty 0)
    else
      let a ← arrayCore anyCore (Array.mkEmpty 4)
      Json.arr a
  else if c = '{' then
    skip; ws
    let c ← peek!
    if c = '}' then
      skip; ws
      Json.obj (RBNode.leaf)
    else
      let kvs ← objectCore anyCore
      Json.obj kvs
  else if c = '\"' then
    skip
    let s ← strCore ""
    ws
    Json.str s
  else if c = 'f' then
    expect "false"; ws
    Json.bool false
  else if c = 't' then
    expect "true"; ws
    Json.bool true
  else if c = 'n' then
    expect "null"; ws
    Json.null
  else if c = '-' ∨ ('0' ≤ c ∧ c ≤ '9') then
    let n ← num
    ws
    Json.num n
  else
    fail "unexpected input"


def any : Quickparse Json := do
  ws
  let res ← anyCore ()
  eoi
  res

end Json.Parser

namespace Json

def parse (s : String) : Except String Lean.Json :=
  match Json.Parser.any s.mkIterator with
  | Quickparse.Result.success _ res => Except.ok res
  | Quickparse.Result.error it err  => Except.error s!"offset {it.i.repr}: {err}"

end Json

end Lean
