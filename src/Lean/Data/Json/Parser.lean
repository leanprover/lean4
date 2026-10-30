/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Gabriel Ebner, Marc Huisinga
-/
module

prelude
public import Lean.Data.Json.Basic
public import Std.Internal.Parsec
import Init.Data.Array.Lemmas
import Init.Data.List.Range

public section

open Std.Internal.Parsec
open Std.Internal.Parsec.String

namespace Lean.Json.Parser

def hexChar : Parser UInt16 := do
  let c ← any
  if '0' <= c && c <= '9' then
    pure $ (c.val - '0'.val).toUInt16
  else if 'a' <= c && c <= 'f' then
    pure $ (c.val - 'a'.val + 10).toUInt16
  else if 'A' <= c && c <= 'F' then
    pure $ (c.val - 'A'.val + 10).toUInt16
  else
    fail "invalid hex character"

def finishSurrogatePair (low : UInt16) : Parser Char := do
  let c ← any
  if c != '\\' then fail ""
  let c ← any
  if c != 'u' then fail ""
  let c ← any
  if c != 'd' && c != 'D' then fail ""
  let u2 ← hexChar; let u3 ← hexChar; let u4 ← hexChar
  let val := (u2 <<< 8) ||| (u3 <<< 4) ||| u4
  if val < 0xC00 then fail "" -- low or not a surrogate
  let charVal := (((low.toUInt32 &&& 0x3FF) <<< 10) ||| (val.toUInt32 &&& 0x3FF)) + 0x10000
  if h : charVal.isValidChar then
    return ⟨charVal, h⟩
  else
    fail "" -- should be unreachable

def escapedChar : Parser Char := do
  let c ← any
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
    let val := (u1 <<< 12) ||| (u2 <<< 8) ||| (u3 <<< 4) ||| u4
    if h : val < 0xD800 then
      return ⟨val.toUInt32, Or.inl h⟩
    else if h' : val < 0xE000 then
      -- low or high surrogate
      if val < 0xDC00 then
        -- low surrogate
        attempt (finishSurrogatePair val) <|> pure '\ufffd'
      else
        -- high/lone surrogate
        return '\ufffd' -- replacement character
    else
      return ⟨val.toUInt32, Or.inr ⟨Nat.not_lt.mp h', Nat.lt_trans val.toFin.isLt (by decide)⟩⟩
  | _ => fail "illegal \\u escape"

partial def strCore (acc : String) : Parser String := do
  let c ← peek!
  if c == '"' then
    skip
    return acc
  else
    let c ← any
    if c == '\\' then
      strCore (acc.push (← escapedChar))
    -- as to whether c.val > 0xffff should be split up and encoded with multiple \u,
    -- the JSON standard is not definite: both directly printing the character
    -- and encoding it with multiple \u is allowed. we choose the former.
    else if 0x0020 <= c.val && c.val <= 0x10ffff then
      strCore (acc.push c)
    else
      fail "unexpected character in string"

@[inline] def str : Parser String := strCore ""

private def smallPowersOfTen : Array Nat := (List.range 19).toArray.map (10 ^ ·)

/-- `10 ^ n`, from a table for the exponents that chunks of digits need. -/
private def powerOfTen (n : Nat) : Nat :=
  if h : n < smallPowersOfTen.size then smallPowersOfTen[n] else 10 ^ n

private theorem powerOfTen_eq (n : Nat) : powerOfTen n = 10 ^ n := by
  rw [powerOfTen]
  split
  · simp [smallPowersOfTen]
  · rfl

/--
Combines `chunks[lo:hi]`, groups of decimal digits in reading order, each paired with its number of
digits, into the number they spell and its number of digits. Splitting in halves keeps the factors
of each multiplication balanced, so this takes subquadratic time in the total number of digits.
-/
private def combineDigitChunks (chunks : Array (Nat × Nat)) (lo hi : Nat) : Nat × Nat :=
  if hi ≤ lo + 1 then
    chunks.getD lo (0, 0)
  else
    let mid := (lo + hi) / 2
    let (a, da) := combineDigitChunks chunks lo mid
    let (b, db) := combineDigitChunks chunks mid hi
    (a * powerOfTen db + b, da + db)
termination_by hi - lo

/-- The digits `x.2` of `x.1` followed by the `y.2` digits of `y.1`. -/
private def appendDigits (x y : Nat × Nat) : Nat × Nat :=
  (x.1 * 10 ^ y.2 + y.1, x.2 + y.2)

private theorem appendDigits_assoc (x y z : Nat × Nat) :
    appendDigits (appendDigits x y) z = appendDigits x (appendDigits y z) := by
  simp only [appendDigits, Nat.pow_add, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

private theorem foldl_appendDigits (l : List (Nat × Nat)) (x : Nat × Nat) :
    l.foldl appendDigits x = appendDigits x (l.foldl appendDigits (0, 0)) := by
  induction l generalizing x with
  | nil => simp [appendDigits]
  | cons y l ih =>
    simp only [List.foldl_cons]
    rw [ih, ih (appendDigits (0, 0) y), ← appendDigits_assoc]
    simp [appendDigits]

/-- The chunks at indices `lo` to `hi - 1`, appended one at a time from left to right. -/
private def appendChunks (chunks : Array (Nat × Nat)) (lo hi : Nat) : Nat × Nat :=
  ((List.range' lo (hi - lo)).map (chunks.getD · (0, 0))).foldl appendDigits (0, 0)

private theorem appendChunks_split (chunks : Array (Nat × Nat)) (lo mid hi : Nat)
    (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    appendChunks chunks lo hi =
      appendDigits (appendChunks chunks lo mid) (appendChunks chunks mid hi) := by
  have hsplit : hi - lo = (mid - lo) + (hi - mid) := by omega
  have hmid : lo + 1 * (mid - lo) = mid := by omega
  simp only [appendChunks]
  rw [hsplit, ← List.range'_append, hmid, List.map_append, List.foldl_append, foldl_appendDigits]

/--
Splitting `chunks[lo:hi]` in halves, as `combineDigitChunks` does, gives the same result as
appending the chunks one at a time from left to right.
-/
private theorem combineDigitChunks_eq (chunks : Array (Nat × Nat)) (lo hi : Nat) (h : lo < hi) :
    combineDigitChunks chunks lo hi = appendChunks chunks lo hi := by
  rw [combineDigitChunks]
  split
  · have : hi - lo = 1 := by omega
    simp [appendChunks, this, appendDigits]
  · dsimp only
    rw [combineDigitChunks_eq chunks lo ((lo + hi) / 2) (by omega),
      combineDigitChunks_eq chunks ((lo + hi) / 2) hi (by omega),
      appendChunks_split chunks lo ((lo + hi) / 2) hi (by omega) (by omega)]
    generalize appendChunks chunks lo ((lo + hi) / 2) = x
    generalize appendChunks chunks ((lo + hi) / 2) hi = y
    obtain ⟨a, da⟩ := x
    obtain ⟨b, db⟩ := y
    simp only [powerOfTen_eq, appendDigits]
termination_by hi - lo

/--
Reads digits into `chunk` until it holds 18 of them, which on 64-bit platforms is as many as fit
without big-number arithmetic, and then moves it to `chunks`. Returns the digits of the last,
partial chunk and the full chunks before it.
-/
private partial def digitChunks (chunk chunkDigits : Nat) (chunks : Array (Nat × Nat)) :
    Parser (Nat × Nat × Array (Nat × Nat)) := do
  if ← isEof then
    return (chunk, chunkDigits, chunks)
  else
    let c ← peek!
    if '0' <= c && c <= '9' then
      skip
      let chunk := 10 * chunk + (c.val - '0'.val).toNat
      if chunkDigits + 1 = 18 then
        digitChunks 0 0 (chunks.push (chunk, 18))
      else
        digitChunks chunk (chunkDigits + 1) chunks
    else
      return (chunk, chunkDigits, chunks)

/--
Reads the rest of a long run of digits, whose value so far is `acc`, and returns the value of the
whole run and `digits` plus the number of digits read here. The digits are read in chunks of 18
that `combineDigitChunks` puts together, so a long run takes time quasi-linear in its length.
-/
private def natLongRun (acc digits : Nat) : Parser (Nat × Nat) := do
  let (chunk, chunkDigits, chunks) ← digitChunks 0 0 #[]
  if chunks.isEmpty then
    return (acc * powerOfTen chunkDigits + chunk, digits + chunkDigits)
  let chunks := if chunkDigits = 0 then chunks else chunks.push (chunk, chunkDigits)
  let (n, d) := combineDigitChunks chunks 0 chunks.size
  return (acc * powerOfTen d + n, digits + d)

/--
Reads digits onto `acc` one at a time, counting them in `digits`; `k` counts the digits read here,
and from the 37th on the rest of the run goes to `natLongRun`. Runs of up to 36 digits, which
include every 64-bit integer, are read without the overhead of chunks.
-/
private partial def natCoreNumDigitsAux (acc digits : Nat) (k : UInt32) : Parser (Nat × Nat) := do
  if ← isEof then
    return (acc, digits)
  else
    let c ← peek!
    if '0' <= c && c <= '9' then
      if k = 36 then
        natLongRun acc digits
      else
        skip
        natCoreNumDigitsAux (10 * acc + (c.val - '0'.val).toNat) (digits + 1) (k + 1)
    else
      return (acc, digits)

/--
Reads the first digits of a run into the machine integer `n`, counting them in `k`, and from the
19th on reads the rest of the run with `natCoreNumDigitsAux`. A number of up to 18 digits is below
`2 ^ 63`, so on 64-bit platforms it is a small `Nat`, and most numbers are read without arithmetic
on `Nat`.
-/
private partial def natCoreNumDigitsSmall (n : UInt64) (k : UInt32) : Parser (Nat × Nat) := do
  if ← isEof then
    return (n.toNat, k.toNat)
  else
    let c ← peek!
    if '0' <= c && c <= '9' then
      if k = 18 then
        natCoreNumDigitsAux n.toNat 18 18
      else
        skip
        natCoreNumDigitsSmall (10 * n + (c.val - '0'.val).toUInt64) (k + 1)
    else
      return (n.toNat, k.toNat)

/--
Reads a run of decimal digits spelling `n` with `d` digits, and returns `acc * 10 ^ d + n` and
`digits + d`.
-/
@[inline] def natCoreNumDigits (acc digits : Nat) : Parser (Nat × Nat) :=
  if acc = 0 && digits = 0 then natCoreNumDigitsSmall 0 0 else natCoreNumDigitsAux acc digits 0

/-- Like `natCoreNumDigitsAux`, without counting the digits. -/
private partial def natCoreAux (acc : Nat) (k : UInt32) : Parser Nat := do
  if ← isEof then
    return acc
  else
    let c ← peek!
    if '0' <= c && c <= '9' then
      if k = 36 then
        return (← natLongRun acc 0).1
      else
        skip
        natCoreAux (10 * acc + (c.val - '0'.val).toNat) (k + 1)
    else
      return acc

/-- Like `natCoreNumDigitsSmall`, without counting the digits. -/
private partial def natCoreSmall (n : UInt64) (k : UInt32) : Parser Nat := do
  if ← isEof then
    return n.toNat
  else
    let c ← peek!
    if '0' <= c && c <= '9' then
      if k = 18 then
        natCoreAux n.toNat 18
      else
        skip
        natCoreSmall (10 * n + (c.val - '0'.val).toUInt64) (k + 1)
    else
      return n.toNat

/-- Reads a run of decimal digits spelling `n` with `d` digits, and returns `acc * 10 ^ d + n`. -/
@[inline] def natCore (acc : Nat) : Parser Nat :=
  if acc = 0 then natCoreSmall 0 0 else natCoreAux acc 0

@[inline]
def lookahead (p : Char → Prop) (desc : String) [DecidablePred p] : Parser Unit := do
  let c ← peek!
  if p c then
    return ()
  else
    fail <| "expected " ++ desc

@[inline]
def natNonZero : Parser Nat := do
  lookahead (fun c => '1' <= c && c <= '9') "1-9"
  natCore 0

@[inline]
def natNumDigits : Parser (Nat × Nat) := do
  lookahead (fun c => '0' <= c && c <= '9') "digit"
  natCoreNumDigits 0 0

@[inline]
def natMaybeZero : Parser Nat := do
  lookahead (fun c => '0' <= c && c <= '9') "0-9"
  natCore 0

@[inline]
def numSign : Parser Int := do
  let c ← peek!
  if c == '-' then
    skip
    return (-1 : Int)
  else
    return 1

@[inline]
def nat : Parser Nat := do
  let c ← peek!
  if c == '0' then
    skip
    return 0
  else
    natNonZero

@[inline]
def numWithDecimals : Parser JsonNumber := do
  let sign ← numSign
  let whole ← nat
  if ← isEof then
    pure <| JsonNumber.fromInt (sign * whole)
  else
    let c ← peek!
    if c == '.' then
      skip
      let (n, d) ← natNumDigits
      if d > USize.size then fail "too many decimals"
      let mantissa' := sign * (whole * (10^d : Nat) + n)
      let exponent' := d
      pure <| JsonNumber.mk mantissa' exponent'
    else
      pure <| JsonNumber.fromInt (sign * whole)

@[inline]
def exponent (value : JsonNumber) : Parser JsonNumber := do
  if ← isEof then
    return value
  else
    let c ← peek!
    if c == 'e' || c == 'E' then
      skip
      let c ← peek!
      if c == '-' then
        skip
        let n ← natMaybeZero
        return value.shiftr n
      else
        if c = '+' then skip
        let n ← natMaybeZero
        -- `shiftl` currently consumes time/memory linear in n,
        -- and panics in `Nat.pow` for sufficiently large n.
        -- This could be improved by supporting positive exponents in `JsonNumber`.
        if n > 100_000 then fail "exponent too large"
        return value.shiftl n
    else
      return value

def num : Parser JsonNumber := do
  let res : JsonNumber ← numWithDecimals
  exponent res

mutual

  partial def arrayCore (acc : Array Json) : Parser (Array Json) := do
    let hd ← anyCore
    let acc' := acc.push hd
    let c ← any
    if c == ']' then
      ws
      return acc'
    else if c == ',' then
      ws
      arrayCore acc'
    else
      fail "unexpected character in array"

  partial def objectCore (kvs : Std.TreeMap.Raw String Json) :
      Parser (Std.TreeMap.Raw String Json) := do
    lookahead (fun c => c == '"') "\""; skip;
    let k ← str; ws
    if kvs.contains k then fail s!"duplicate object key {k.quote}"
    lookahead (fun c => c == ':') ":"; skip; ws
    let v ← anyCore
    let c ← any
    if c == '}' then
      ws
      return kvs.insert k v
    else if c == ',' then
      ws
      objectCore (kvs.insert k v)
    else
      fail "unexpected character in object"

  partial def anyCore : Parser Json := do
    let c ← peek!
    if c == '[' then
      skip; ws
      let c ← peek!
      if c == ']' then
        skip; ws
        return Json.arr (Array.mkEmpty 0)
      else
        let a ← arrayCore (Array.mkEmpty 4)
        return Json.arr a
    else if c == '{' then
      skip; ws
      let c ← peek!
      if c == '}' then
        skip; ws
        return Json.obj ∅
      else
        let kvs ← objectCore ∅
        return Json.obj kvs
    else if c == '\"' then
      skip
      let s ← str
      ws
      return Json.str s
    else if c == 'f' then
      skipString "false"; ws
      return Json.bool false
    else if c == 't' then
      skipString "true"; ws
      return Json.bool true
    else if c == 'n' then
      skipString "null"; ws
      return Json.null
    else if c == '-' || ('0' <= c && c <= '9') then
      let n ← num
      ws
      return Json.num n
    else
      fail "unexpected input"

end

def any : Parser Json := do
  ws
  let res ← anyCore
  eof
  return res

end Json.Parser

namespace Json

/-- Parses a JSON value, surrounded by optional whitespace. Objects with duplicate keys are rejected. -/
def parse (s : String) : Except String Lean.Json :=
  Parser.run Json.Parser.any s

end Json

end Lean
