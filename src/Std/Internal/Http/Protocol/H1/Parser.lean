/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Parsec
public import Std.Internal.Http.Data
public import Std.Internal.Parsec.ByteArray

namespace Std
namespace Http
namespace Protocol
namespace H1

open Std Internal Parsec ByteArray Util

/-!
This module defines a parser for HTTP/1.1 requests. The reference used is https://httpwg.org/specs/rfc9112.html.
-/

set_option linter.all true

@[inline]
def isDigit (c : UInt8) : Bool :=
  c ≥ '0'.toUInt8 ∧ c ≤ '9'.toUInt8

@[inline]
def isAlpha (c : UInt8) : Bool :=
  (c ≥ 'a'.toUInt8 ∧ c ≤ 'z'.toUInt8) ∨ (c ≥ 'A'.toUInt8 ∧ c ≤ 'Z'.toUInt8)

@[inline]
def isVChar (c : UInt8) : Bool :=
  c ≥ 0x21 ∧ c ≤ 128

def isTokenCharacter (c : UInt8) : Bool :=
  isDigit c ∨ isAlpha c ∨ c == '!'.toUInt8 ∨ c == '#'.toUInt8 ∨ c == '$'.toUInt8 ∨ c == '%'.toUInt8 ∨
  c == '&'.toUInt8 ∨   c == '\''.toUInt8 ∨ c == '*'.toUInt8 ∨  c == '+'.toUInt8 ∨ c == '-'.toUInt8 ∨
  c == '.'.toUInt8 ∨  c == '^'.toUInt8 ∨ c == '_'.toUInt8 ∨ c == '`'.toUInt8 ∨   c == '|'.toUInt8 ∨
  c == '~'.toUInt8

@[inline]
def isObsChar (c : UInt8) : Bool :=
  c ≥ 0x80 ∧ c ≤ 0xFF

@[inline]
def isFieldVChar (c : UInt8) : Bool :=
  isVChar c ∨ isObsChar c

-- HTAB / SP / %x21 / %x23-5B / %x5D-7E / obs-text
@[inline]
def isQdText (c : UInt8) : Bool :=
  c == '\t'.toUInt8 ∨
  c == ' '.toUInt8 ∨
  c == '!'.toUInt8 ∨
  (c ≥ '#'.toUInt8 ∧ c ≤ '['.toUInt8) ∨
  (c ≥ ']'.toUInt8 ∧ c ≤ '~'.toUInt8) ∨
  isObsChar c

-- Parser blocks

def manyItems {α : Type} (parser : Parser (Option α)) (maxCount : Nat) : Parser (Array α) := do
  let items ← many (parser.bind (fun item => match item with
    | some x => return x
    | none => fail "end of items"))
  if items.size > maxCount then
    fail s!"Too many items: {items.size} > {maxCount}"
  return items

def opt (x : Option α) : Parser α :=
  if let some res := x then
    return res
  else
    fail "expected value but got none"

@[inline]
def token (limit : Nat) : Parser ByteSlice :=
  takeWhileUpTo1 isTokenCharacter limit

@[inline]
def crlf : Parser Unit :=
  skipBytes "\r\n".toUTF8

@[inline]
def rsp : Parser Unit :=
  discard <| takeWhileUpTo1 (· == ' '.toUInt8) 256

@[inline]
def osp : Parser Unit :=
  discard <| takeWhileUpTo (· == ' '.toUInt8) 256

@[inline]
def uint8 : Parser UInt8 := do
  let d ← digit
  return d.toUInt8

def hexDigit : Parser UInt8 := do
  let b ← any
  if b ≥ '0'.toUInt8 && b ≤ '9'.toUInt8 then return b - '0'.toUInt8
  else if b ≥ 'A'.toUInt8 && b ≤ 'F'.toUInt8 then return b - 'A'.toUInt8 + 10
  else if b ≥ 'a'.toUInt8 && b ≤ 'f'.toUInt8 then return b - 'a'.toUInt8 + 10
  else fail s!"Invalid hex digit {Char.ofUInt8 b |>.quote}"

@[inline]
def hex : Parser Nat := do
  let hexDigits ← many1 (attempt hexDigit)
  return (hexDigits.foldl (fun acc cur => acc * 16 + cur.toNat) 0)

-- Actual parsers

-- HTTP-version  = HTTP-name "/" DIGIT "." DIGIT
-- HTTP-name     = %s"HTTP"
def parseHttpVersion : Parser Version := do
  skipBytes "HTTP/".toUTF8
  let major ← uint8
  skipByte '.'.toUInt8
  let minor ← uint8
  opt <| Version.fromNumber? (major - 48 |>.toNat) (minor - 48 |>.toNat)

--   method         = token
def parseMethod : Parser Method := do
  let method ← token 16
  opt <| Method.fromString? (String.fromUTF8! method.toByteArray)

def parseURI : Parser String := do
  let uri ← takeUntil (· == ' '.toUInt8)
  return String.fromUTF8! uri.toByteArray

/--
Parses a request line

request-line   = method SP request-target SP HTTP-version
-/
public def parseRequestLine : Parser Request.Head := do
  let method ← parseMethod <* rsp
  let uri ← Std.Http.Parser.parseRequestTarget <* rsp
  let version ← parseHttpVersion <* crlf
  return ⟨method, version, uri, .empty⟩

-- field-line   = field-name ":" OWS field-value OWS
def parseFieldLine (headerLimit : Nat) : Parser (String × String) := do
  (String.fromUTF8! ·.toByteArray, String.fromUTF8! ·.toByteArray) <$>
  token 256 <*> (skipByte ':'.toUInt8 *> osp *> takeWhileUpTo1 isFieldVChar headerLimit <* osp)

/--
Parses a single header.

field-line CRLF / CRLF
-/
public def parseSingleHeader (headerLimit : Nat) : Parser (Option (String × String)) :=
  optional (attempt <| parseFieldLine headerLimit) <* crlf

-- quoted-pair = "\" ( HTAB / SP / VCHAR / obs-text )
def parseQuotedPair : Parser UInt8 := do
  skipByte '\\'.toUInt8
  let b ← any

  if b == '\t'.toUInt8 ∨ b == ' '.toUInt8 || isVChar b || isObsChar b then
    return b
  else
    fail s!"invalid quoted-pair byte: {Char.ofUInt8 b |>.quote}"

-- quoted-string = DQUOTE *( qdtext / quoted-pair ) DQUOTE
partial def parseQuotedString : Parser String := do
  skipByte '"'.toUInt8

  let rec loop (buf : ByteArray) : Parser ByteArray := do
    let b ← any

    if b == '"'.toUInt8 then
      return buf
    else if b == '\\'.toUInt8 then
      let next ← any
      if next == '\t'.toUInt8 ∨ next == ' '.toUInt8 ∨ isVChar next ∨ isObsChar next
        then loop (buf.push next)
        else fail s!"invalid quoted-pair byte: {Char.ofUInt8 next |>.quote}"
    else if isQdText b then
      loop (buf.push b)
    else
      fail s!"invalid qdtext byte: {Char.ofUInt8 b |>.quote}"

  return String.fromUTF8! (← loop .empty)

-- chunk-ext = *( BWS ";" BWS chunk-ext-name [ BWS "=" BWS chunk-ext-val] )
def parseChunkExt : Parser (String × Option String) := do
  osp *> skipByte ';'.toUInt8 *> osp
  let name ← (String.fromUTF8! <$> ByteSlice.toByteArray <$> token 256) <* osp

  if (← peekWhen? (· == '='.toUInt8)) |>.isSome then
    osp *> skipByte '='.toUInt8 *> osp
    let value ← osp *> (parseQuotedString <|> String.fromUTF8! <$> ByteSlice.toByteArray <$> token 256)
    return (name, some value)

  return (name, none)

/--
This function parses the size and extension of a chunk
-/
public def parseChunkSize : Parser (Nat × Array (String × Option String)) := do
  let size ← hex
  let ext ← many parseChunkExt
  crlf
  return (size, ext)

/--
Result of parsing partial or complete information.
-/
public inductive TakeResult
  | complete (data : ByteSlice)
  | incomplete (data : ByteSlice) (remaining : Nat)

/--
Parses a fixed size data that can be incomplete.
-/
public def parseFixedSizeData (size : Nat) : Parser TakeResult := fun it =>
  if it.remainingBytes = 0 then
    .error it .eof
  else if it.remainingBytes < size then
    .success (it.forward it.remainingBytes) (.incomplete it.array[it.idx...(it.idx+it.remainingBytes)] (size - it.remainingBytes))
  else
    .success (it.forward size) (.complete (it.array[it.idx...(it.idx+size)]))

/--
Parses a fixed size data that can be incomplete.
-/
public def parseChunkedSizedData (size : Nat) : Parser TakeResult := do
  match ← parseFixedSizeData size with
  | .complete data => crlf *> return .complete data
  | .incomplete data res => return .incomplete data res

/--
This function parses a single chunk in chunked transfer encoding
-/
public def parseChunk : Parser (Option (Nat × Array (String × Option String) × ByteSlice)) := do
  let (size, ext) ← parseChunkSize
  if size == 0 then
    return none
  else
    let data ← take size
    return some ⟨size, ext, data⟩
/--
This function parses a trailer header (used after chunked body)
-/
def parseTrailerHeader (headerLimit : Nat) : Parser (Option (String × String)) := parseSingleHeader headerLimit

/--
This function parses trailer headers after chunked body
-/
public def parseTrailers (headerLimit : Nat) : Parser (Array  (String × String)) := do
  let trailers ← manyItems (parseTrailerHeader headerLimit) 100
  crlf
  return trailers

end H1
end Protocol
end Http
end Std
