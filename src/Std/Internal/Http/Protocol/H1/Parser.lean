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
public import Std.Internal.Http.Protocol.H1.Config

/-!
This module defines a parser for HTTP/1.1 requests. The reference used is https://httpwg.org/specs/rfc9112.html.
-/

namespace Std.Http.Protocol.H1

open Std Internal Parsec ByteArray Internal

set_option linter.all true

@[inline]
def isDigit (c : UInt8) : Bool :=
  c ≥ '0'.toUInt8 ∧ c ≤ '9'.toUInt8

@[inline]
def isAlpha (c : UInt8) : Bool :=
  (c ≥ 'a'.toUInt8 ∧ c ≤ 'z'.toUInt8) ∨ (c ≥ 'A'.toUInt8 ∧ c ≤ 'Z'.toUInt8)

@[inline]
def isVChar (c : UInt8) : Bool :=
  c ≥ 0x21 ∧ c ≤ 0x7E

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
  isVChar c ∨ isObsChar c ∨ c = ' '.toUInt8 ∨ c = '\t'.toUInt8

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
  let items ← many (attempt <| parser.bind (fun item => match item with
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
def crlf : Parser Unit := do
  discard <| optional (skipByte '\r'.toUInt8)
  skipByte '\n'.toUInt8

@[inline]
def rsp (limits : H1.Config) : Parser Unit := do
  discard <| takeWhileUpTo1 (· == ' '.toUInt8) limits.maxSpaceSequence

  if (← peekWhen? (· == ' '.toUInt8)) |>.isSome then
    fail "invalid space sequence"
  else
    pure ()

@[inline]
def osp (limits : H1.Config) : Parser Unit := do
  discard <| takeWhileUpTo (· == ' '.toUInt8) limits.maxSpaceSequence

  if (← peekWhen? (· == ' '.toUInt8)) |>.isSome then
    fail "invalid space sequence"
  else
    pure ()

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
  opt <| Version.ofNumber? (major - 48 |>.toNat) (minor - 48 |>.toNat)

--   method         = token
def parseMethod : Parser Method :=
  (skipBytes "GET".toUTF8 <&> fun _ => Method.get)
  <|> (skipBytes "HEAD".toUTF8 <&> fun _ => Method.head)
  <|> (attempt <| skipBytes "POST".toUTF8 <&> fun _ => Method.post)
  <|> (attempt <| skipBytes "PUT".toUTF8 <&> fun _ => Method.put)
  <|> (skipBytes "DELETE".toUTF8 <&> fun _ => Method.delete)
  <|> (skipBytes "CONNECT".toUTF8 <&> fun _ => Method.connect)
  <|> (skipBytes "OPTIONS".toUTF8 <&> fun _ => Method.options)
  <|> (skipBytes "TRACE".toUTF8 <&> fun _ => Method.trace)
  <|> (skipBytes "PATCH".toUTF8 <&> fun _ => Method.patch)

def parseURI (limits : H1.Config) : Parser ByteArray := do
  let uri ← takeUntilUpTo (· == ' '.toUInt8) limits.maxUriLength
  return uri.toByteArray

/--
Parses a request line

request-line   = method SP request-target SP HTTP-version
-/
public def parseRequestLine (limits : H1.Config) : Parser Request.Head := do
  let method ← parseMethod <* rsp limits
  let uri ← parseURI limits <* rsp limits

  let uri ← match (Std.Http.URI.Parser.parseRequestTarget <* eof).run uri with
  | .ok res => pure res
  | .error res => fail res

  let version ← parseHttpVersion <* crlf
  return ⟨method, version, uri, .empty⟩

-- field-line   = field-name ":" OWS field-value OWS
def parseFieldLine (limits : H1.Config) : Parser (String × String) := do
  let name ← token limits.maxHeaderNameLength
  let value ← skipByte ':'.toUInt8 *> osp limits *> optional (takeWhileUpTo isFieldVChar limits.maxHeaderValueLength) <* osp limits

  let name ← opt <| String.fromUTF8? name.toByteArray
  let value ← opt <| String.fromUTF8? <| value.map (·.toByteArray) |>.getD .empty

  return (name, value)

/--
Parses a single header.

field-line CRLF / CRLF
-/
public def parseSingleHeader (limits : H1.Config) : Parser (Option (String × String)) := do
  let next ← peek?
  if next == some '\r'.toUInt8 ∨ next == some '\n'.toUInt8 then
    crlf
    pure none
  else
    some <$> (parseFieldLine limits <* crlf)

-- quoted-pair = "\" ( HTAB / SP / VCHAR / obs-text )
def parseQuotedPair : Parser UInt8 := do
  skipByte '\\'.toUInt8
  let b ← any

  if b == '\t'.toUInt8 ∨ b == ' '.toUInt8 ∨ isVChar b ∨ isObsChar b then
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

  opt <| String.fromUTF8? (← loop .empty)

-- chunk-ext = *( BWS ";" BWS chunk-ext-name [ BWS "=" BWS chunk-ext-val] )
def parseChunkExt (limits : H1.Config) : Parser (ExtensionName × Option String) := do
  osp limits *> skipByte ';'.toUInt8 *> osp limits
  let name ← (opt =<< String.fromUTF8? <$> ByteSlice.toByteArray <$> token limits.maxChunkExtNameLength) <* osp limits

  let some name := ExtensionName.ofString? name
    | fail "invalid extension name"

  if (← peekWhen? (· == '='.toUInt8)) |>.isSome then
    osp limits *> skipByte '='.toUInt8 *> osp limits
    let value ← osp limits *> (parseQuotedString <|> opt =<< (String.fromUTF8? <$> ByteSlice.toByteArray <$> token limits.maxChunkExtValueLength))

    return (name, some value)

  return (name, none)

/--
This function parses the size and extension of a chunk
-/
public def parseChunkSize (limits : H1.Config) : Parser (Nat × Array (ExtensionName × Option String)) := do
  let size ← hex
  let ext ← many (parseChunkExt limits)
  crlf
  return (size, ext)

/--
Result of parsing partial or complete information.
-/
public inductive TakeResult
  | complete (data : ByteSlice)
  | incomplete (data : ByteSlice) (remaining : Nat)

/--
This function parses a single chunk in chunked transfer encoding
-/
public def parseChunk (limits : H1.Config) : Parser (Option (Nat × Array (ExtensionName × Option String) × ByteSlice)) := do
  let (size, ext) ← parseChunkSize limits
  if size == 0 then
    return none
  else
    let data ← take size
    return some ⟨size, ext, data⟩

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
This function parses a trailer header (used after chunked body)
-/
def parseTrailerHeader (limits : H1.Config) : Parser (Option (String × String)) := parseSingleHeader limits

/--
This function parses trailer headers after chunked body
-/
public def parseTrailers (limits : H1.Config) : Parser (Array (String × String)) := do
  let trailers ← manyItems (parseTrailerHeader limits) limits.maxTrailerHeaders
  crlf
  return trailers

/--
Parses HTTP status code (3 digits)
-/
def parseStatusCode : Parser Status := do
  let d1 ← digit
  let d2 ← digit
  let d3 ← digit
  let code := (d1.toNat - 48) * 100 + (d2.toNat - 48) * 10 + (d3.toNat - 48)

  return Status.ofCode code.toUInt16

/--
Parses reason phrase (text after status code)
-/
def parseReasonPhrase (limits : H1.Config) : Parser String := do
  let bytes ← takeWhileUpTo (fun c => c != '\r'.toUInt8) limits.maxReasonPhraseLength
  opt <| String.fromUTF8? bytes.toByteArray

/--
Parses a status line

status-line = HTTP-version SP status-code SP [ reason-phrase ]
-/
public def parseStatusLine (limits : H1.Config) : Parser Response.Head := do
  let version ← parseHttpVersion <* rsp limits
  let status ← parseStatusCode <* rsp limits
  discard <| parseReasonPhrase limits <* crlf
  return ⟨status, version, .empty⟩

/--
This function parses the body of the last chunk.
-/
public def parseLastChunkBody (limits : H1.Config) : Parser Unit := do
  discard <| manyItems (parseTrailerHeader limits) limits.maxTrailerHeaders
  crlf

end Std.Http.Protocol.H1
