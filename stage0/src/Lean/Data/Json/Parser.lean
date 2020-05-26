/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Marc Huisinga
-/
prelude
import Lean.Data.Json.Basic
import Init.Control.Except

namespace Lean

inductive Quickparse.Result (α : Type)
| success (pos : String.Iterator) (res : α) : Quickparse.Result
| error (pos : String.Iterator) (err : String) : Quickparse.Result

def Quickparse (α : Type) : Type := String.Iterator → Quickparse.Result α

instance Quickparse.inhabited (α : Type) : Inhabited (Quickparse α) :=
⟨fun it => Quickparse.Result.error it ""⟩

namespace Quickparse

open Result

partial def skipWs : String.Iterator → String.Iterator | it =>
if it.hasNext then
  let c := it.curr;
  if c = '\u0009' ∨ c = '\u000a' ∨ c = '\u000d' ∨ c = '\u0020' then
    skipWs it.next
  else
    it
else
 it

@[inline]
protected def pure {α : Type} (a : α) : Quickparse α | it =>
success it a

@[inline]
protected def bind {α β : Type} (f : Quickparse α) (g : α → Quickparse β) : Quickparse β | it =>
match f it with
| success rem a => g a rem
| error pos msg => error pos msg

@[inline]
def fail {α : Type} (msg : String) : Quickparse α | it =>
error it msg

@[inline]
instance : Monad Quickparse :=
{ pure := @Quickparse.pure, bind := @Quickparse.bind }

def unexpectedEndOfInput := "unexpected end of input"

@[inline]
def peek? : Quickparse (Option Char) | it =>
if it.hasNext then
  success it it.curr
else
  success it none

@[inline]
def peek! : Quickparse Char := do
some c <- peek? | fail unexpectedEndOfInput;
pure c

@[inline]
def skip : Quickparse Unit | it =>
success it.next ()

@[inline]
def next : Quickparse Char := do
c ← peek!; skip;
pure c

def expect (s : String) : Quickparse Unit | it =>
if it.extract (it.forward s.length) = s then
  success (it.forward s.length) ()
else
  error it ("expected: " ++ s)

@[inline]
def ws : Quickparse Unit | it =>
success (skipWs it) ()

def expectedEndOfInput := "expected end of input"

@[inline]
def eoi : Quickparse Unit | it =>
if it.hasNext then
  error it expectedEndOfInput
else
  success it ()

end Quickparse

namespace Json.Parser

open Quickparse

@[inline]
def hexChar : Quickparse Nat := do
c ← next;
if '0' ≤ c ∧ c ≤ '9' then
  pure $ c.val.toNat - '0'.val.toNat
else if 'a' ≤ c ∧ c ≤ 'f' then
  pure $ c.val.toNat - 'a'.val.toNat
else if 'A' ≤ c ∧ c ≤ 'F' then
  pure $ c.val.toNat - 'A'.val.toNat
else
  fail "invalid hex character"

def escapedChar : Quickparse Char := do
c ← next;
match c with
| '\\' => pure '\\'
| '"'  => pure '"'
| '/'  => pure '/'
| 'b'  => pure '\x08'
| 'f'  => pure '\x0c'
| 'n'  => pure '\n'
| 'r'  => pure '\x0d'
| 't'  => pure '\t'
| 'u'  => do
  u1 ← hexChar; u2 ← hexChar; u3 ← hexChar; u4 ← hexChar;
  pure $ Char.ofNat $ 4096*u1 + 256*u2 + 16*u3 + u4
| _ => fail "illegal \\u escape"

partial def strCore : String → Quickparse String | acc => do
c ← peek!;
if c = '"' then do -- "
  skip;
  pure acc
else do
  c ← next;
  ec ←
    if c = '\\' then
      escapedChar
    -- as to whether c.val > 0xffff should be split up and encoded with multiple \u,
    -- the JSON standard is not definite: both directly printing the character
    -- and encoding it with multiple \u is allowed. we choose the former.
    else if 0x0020 ≤ c.val ∧ c.val ≤ 0x10ffff then
      pure c
    else
      fail "unexpected character in string";
  strCore (acc.push ec)

def str : Quickparse String := strCore ""

partial def natCore : Nat → Nat → Quickparse (Nat × Nat) | acc, digits => do
some c ← peek? | pure (acc, digits);
if '0' ≤ c ∧ c ≤ '9' then do
  skip;
  let acc' := 10*acc + (c.val.toNat - '0'.val.toNat);
  natCore acc' (digits+1)
else
  pure (acc, digits)

@[inline]
def lookahead (p : Char → Prop) (desc : String) [DecidablePred p] : Quickparse Unit := do
c <- peek!;
if p c then
  pure ()
else
  fail $ "expected " ++ desc

@[inline]
def natNonZero : Quickparse Nat := do
lookahead (fun c => '1' ≤ c ∧ c ≤ '9') "1-9";
(n, _) ← natCore 0 0;
pure n

@[inline]
def natNumDigits : Quickparse (Nat × Nat) := do
lookahead (fun c => '0' ≤ c ∧ c ≤ '9') "digit";
natCore 0 0

@[inline]
def natMaybeZero : Quickparse Nat := do
(n, _) ← natNumDigits;
pure n

def num : Quickparse JsonNumber := do
c ← peek!;
sign ←
  if c = '-' then do
    skip;
    pure (-1 : Int)
  else
    pure 1;
c ← peek!;
res ←
  if c = '0' then do
    skip;
    pure 0
  else
    natNonZero;
let res := JsonNumber.fromInt (sign * res);
c? ← peek?;
res ←
  if c? = some '.' then do
    skip;
    (n, d) ← natNumDigits;
    if d > usizeSz then do fail "too many decimals" else pure ();
    let mantissa' := res.mantissa * (10^d : Nat) + n;
    let exponent' := res.exponent + d;
    pure $ JsonNumber.mk mantissa' exponent'
  else
    pure res;
c? ← peek?;
if c? = some 'e' ∨ c? = some 'E' then do
  skip;
  c ← peek!;
  if c = '-' then do
    skip;
    n ← natMaybeZero;
    pure (res.shiftr n)
  else do
    if c = '+' then skip else pure ();
    n ← natMaybeZero;
    if n > usizeSz then do fail "exp too large" else pure ();
    pure (res.shiftl n)
else pure res

partial def arrayCore (anyCore : Unit → Quickparse Json) : Array Json → Quickparse (Array Json) | acc => do
hd ← anyCore ();
let acc' := acc.push hd;
c ← next;
if c = ']' then do
  ws;
  pure acc'
else if c = ',' then do
  ws;
  arrayCore acc'
else
  fail "unexpected character in array"

partial def objectCore : (Unit → Quickparse Json) → Quickparse (RBNode String (fun _ => Json)) | anyCore => do
lookahead (fun c => c = '"') "\""; skip; -- "
k ← strCore ""; ws;
lookahead (fun c => c = ':') ":"; skip; ws;
v ← anyCore ();
c ← next;
if c = '}' then do
  ws;
  pure (RBNode.singleton k v)
else if c = ',' then do
  ws;
  kvs ← objectCore anyCore;
  pure (kvs.insert strLt k v)
else
  fail "unexpected character in object"

-- takes a unit parameter so that
-- we can use the equation compiler and recursion
partial def anyCore : Unit → Quickparse Json | () => do
c ← peek!;
if c = '[' then do
  skip; ws;
  c ← peek!;
  if c = ']' then do
    skip; ws;
    pure (Json.arr (Array.mkEmpty 0))
  else do
    a ← arrayCore anyCore (Array.mkEmpty 4);
    pure (Json.arr a)
else if c = '{' then do
  skip; ws;
  c ← peek!;
  if c = '}' then do
    skip; ws;
    pure (Json.obj (RBNode.leaf))
  else do
    kvs ← objectCore anyCore;
    pure (Json.obj kvs)
else if c = '"' then do --"
  skip;
  s ← strCore ""; ws;
  pure (Json.str s)
else if c = 'f' then do
  expect "false"; ws;
  pure (Json.bool false)
else if c = 't' then do
  expect "true"; ws;
  pure (Json.bool true)
else if c = 'n' then do
  expect "null"; ws;
  pure Json.null
else if c = '-' ∨ ('0' ≤ c ∧ c ≤ '9') then do
  n ← num; ws;
  pure (Json.num n)
else
  fail "unexpected input"


def any : Quickparse Json := do
ws;
res ← anyCore ();
eoi;
pure res

end Json.Parser

namespace Json

def parse (s : String) : Except String Lean.Json :=
match Json.Parser.any s.mkIterator with
| Result.success _ res => Except.ok res
| Result.error it err  => Except.error ("offset " ++ it.i.repr ++ ": " ++ err)

end Json

end Lean
