/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Marc Huisinga
-/
import Lean.Data.Json.Basic
import Lean.Data.Parsec

namespace Lean.Json.Parser

open Lean.Parsec

@[inline]
def hexChar : Parsec Nat := do
  let c ← anyChar
  if '0' ≤ c ∧ c ≤ '9' then
    pure $ c.val.toNat - '0'.val.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then
    pure $ c.val.toNat - 'a'.val.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then
    pure $ c.val.toNat - 'A'.val.toNat + 10
  else
    fail "invalid hex character"

def escapedChar : Parsec Char := do
  let c ← anyChar
  match c with
  | '\\' => return '\\'
  | '"'  => return '"'
  | '/'  => return '/'
  | 'b'  => return '\x08'
  | 'f'  => return '\x0c'
  | 'n'  => return '\n'
  | 'r'  => return '\x0d'
  | 't'  => return '\t'
  | 'u'  =>
    let u1 ← hexChar; let u2 ← hexChar; let u3 ← hexChar; let u4 ← hexChar
    return Char.ofNat $ 4096*u1 + 256*u2 + 16*u3 + u4
  | _ => fail "illegal \\u escape"

partial def strCore (acc : String) : Parsec String := do
  let c ← peek!
  if c = '"' then -- "
    skip
    return acc
  else
    let c ← anyChar
    if c = '\\' then
      strCore (acc.push (← escapedChar))
    -- as to whether c.val > 0xffff should be split up and encoded with multiple \u,
    -- the JSON standard is not definite: both directly printing the character
    -- and encoding it with multiple \u is allowed. we choose the former.
    else if 0x0020 ≤ c.val ∧ c.val ≤ 0x10ffff then
      strCore (acc.push c)
    else
      fail "unexpected character in string"

def str : Parsec String := strCore ""

partial def natCore (acc digits : Nat) : Parsec (Nat × Nat) := do
  let some c ← peek? | return (acc, digits)
  if '0' ≤ c ∧ c ≤ '9' then
    skip
    let acc' := 10*acc + (c.val.toNat - '0'.val.toNat)
    natCore acc' (digits+1)
  else
    return (acc, digits)

@[inline]
def lookahead (p : Char → Prop) (desc : String) [DecidablePred p] : Parsec Unit := do
  let c ← peek!
  if p c then
    return ()
  else
    fail <| "expected " ++ desc

@[inline]
def natNonZero : Parsec Nat := do
  lookahead (fun c => '1' ≤ c ∧ c ≤ '9') "1-9"
  let (n, _) ← natCore 0 0
  return n

@[inline]
def natNumDigits : Parsec (Nat × Nat) := do
  lookahead (fun c => '0' ≤ c ∧ c ≤ '9') "digit"
  natCore 0 0

@[inline]
def natMaybeZero : Parsec Nat := do
  let (n, _) ← natNumDigits
  return n

def num : Parsec JsonNumber := do
  let c ← peek!
  let sign ← if c = '-' then
    skip
    pure (-1 : Int)
  else
    pure 1
  let c ← peek!
  let res ← if c = '0' then
    skip
    pure 0
  else
    natNonZero
  let c? ← peek?
  let res : JsonNumber ← if c? = some '.' then
    skip
    let (n, d) ← natNumDigits
    if d > USize.size then fail "too many decimals"
    let mantissa' := sign * (res * (10^d : Nat) + n)
    let exponent' := d
    pure <| JsonNumber.mk mantissa' exponent'
  else
    pure <| JsonNumber.fromInt (sign * res)
  let c? ← peek?
  if c? = some 'e' ∨ c? = some 'E' then
    skip
    let c ← peek!
    if c = '-' then
      skip
      let n ← natMaybeZero
      return res.shiftr n
    else
      if c = '+' then skip
      let n ← natMaybeZero
      if n > USize.size then fail "exp too large"
      return res.shiftl n
  else
    return res

partial def arrayCore (anyCore : Parsec Json) (acc : Array Json) : Parsec (Array Json) := do
  let hd ← anyCore
  let acc' := acc.push hd
  let c ← anyChar
  if c = ']' then
    ws
    return acc'
  else if c = ',' then
    ws
    arrayCore anyCore acc'
  else
    fail "unexpected character in array"

partial def objectCore (anyCore : Parsec Json) : Parsec (RBNode String (fun _ => Json)) := do
  lookahead (fun c => c = '"') "\""; skip; -- "
  let k ← strCore ""; ws
  lookahead (fun c => c = ':') ":"; skip; ws
  let v ← anyCore
  let c ← anyChar
  if c = '}' then
    ws
    return RBNode.singleton k v
  else if c = ',' then
    ws
    let kvs ← objectCore anyCore
    return kvs.insert compare k v
  else
    fail "unexpected character in object"

partial def anyCore : Parsec Json := do
  let c ← peek!
  if c = '[' then
    skip; ws
    let c ← peek!
    if c = ']' then
      skip; ws
      return Json.arr (Array.mkEmpty 0)
    else
      let a ← arrayCore anyCore (Array.mkEmpty 4)
      return Json.arr a
  else if c = '{' then
    skip; ws
    let c ← peek!
    if c = '}' then
      skip; ws
      return Json.obj (RBNode.leaf)
    else
      let kvs ← objectCore anyCore
      return Json.obj kvs
  else if c = '\"' then
    skip
    let s ← strCore ""
    ws
    return Json.str s
  else if c = 'f' then
    skipString "false"; ws
    return Json.bool false
  else if c = 't' then
    skipString "true"; ws
    return Json.bool true
  else if c = 'n' then
    skipString "null"; ws
    return Json.null
  else if c = '-' ∨ ('0' ≤ c ∧ c ≤ '9') then
    let n ← num
    ws
    return Json.num n
  else
    fail "unexpected input"


def any : Parsec Json := do
  ws
  let res ← anyCore
  eof
  return res

end Json.Parser

namespace Json

def parse (s : String) : Except String Lean.Json :=
  match Json.Parser.any s.mkIterator with
  | Parsec.ParseResult.success _ res => Except.ok res
  | Parsec.ParseResult.error it err  => Except.error s!"offset {repr it.i.byteIdx}: {err}"

end Json

end Lean
