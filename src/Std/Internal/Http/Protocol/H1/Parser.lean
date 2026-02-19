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
This module defines parsers for HTTP/1.1 request and response lines, headers, and body framing. The
reference used is https://httpwg.org/specs/rfc9112.html.
-/

namespace Std.Http.Protocol.H1

open Std Internal Parsec ByteArray Internal Internal.Char

set_option linter.all true

@[inline]
def isVChar (c : UInt8) : Bool :=
  c ≥ 0x21 ∧ c ≤ 0x7E

@[inline]
def isObsChar (c : UInt8) : Bool :=
  c ≥ 0x80 ∧ c ≤ 0xFF

/--
Checks if a byte may appear inside a field value.

RFC 9110 §5.5 defines `field-vchar = VCHAR / obs-text`, but also permits embedded SP/HTAB
between non-whitespace characters within a field value. This predicate covers all bytes that
may appear anywhere inside a field value (including interior whitespace), so callers do not
need to special-case them.
-/
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


partial def manyItems {α : Type} (parser : Parser (Option α)) (maxCount : Nat) : Parser (Array α) := do
  let rec go (acc : Array α) : Parser (Array α) := do
    let step ← optional <| attempt do
      match ← parser with
      | none => fail "end of items"
      | some x => return x

    match step with
    | none =>
      return acc
    | some x =>
      let acc := acc.push x

      if acc.size + 1 > maxCount then
        fail s!"Too many items: {acc.size} > {maxCount}"

      go acc
  go #[]


/--
Lifts an `Option` into the parser monad, failing with a generic message if the value is `none`.
-/
def liftOption (x : Option α) : Parser α :=
  if let some res := x then
    return res
  else
    fail "expected value but got none"

/--
Parses an HTTP token (RFC 9110 §5.6.2): one or more token characters, up to `limit` bytes.
Fails if the input starts with a non-token character or is empty.
-/
@[inline]
def token (limit : Nat) : Parser ByteSlice :=
  takeWhileUpTo1 (fun c => isTokenCharacter (Char.ofUInt8 c)) limit

/--
Parses a line terminator.
-/
@[inline]
def crlf : Parser Unit := do
  discard <| optional (skipByte '\r'.toUInt8)
  skipByte '\n'.toUInt8

/--
Parses a single space (SP, 0x20).
-/
@[inline]
def sp : Parser Unit :=
  skipByte ' '.toUInt8

/--
Parses optional whitespace (OWS = *(SP / HTAB), RFC 9110 §5.6.3), bounded by
`limits.maxSpaceSequence`. Fails if more whitespace follows the limit, so oversized
padding is rejected rather than silently truncated.
-/
@[inline]
def ows (limits : H1.Config) : Parser Unit := do
  discard <| takeWhileUpTo (fun c => c == ' '.toUInt8 || c == '\t'.toUInt8) limits.maxSpaceSequence

  if (← peekWhen? (fun c => c == ' '.toUInt8 || c == '\t'.toUInt8)) |>.isSome then
    fail "invalid space sequence"
  else
    pure ()

/--
Parses a single ASCII decimal digit and returns it as a `UInt8` (value 0–9 as raw byte).
-/
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

partial def hex : Parser Nat := do
  let rec go (acc : Nat) (count : Nat) : Parser Nat := do
    match ← optional (attempt hexDigit) with
    | some d =>
        if count + 1 > 16 then
          fail "chunk size too large"
        else
          go (acc * 16 + d.toNat) (count + 1)
    | none =>
        if count = 0 then
          fail "expected hex digit"
        else
          return acc
  go 0 0

-- Actual parsers

-- HTTP-version  = HTTP-name "/" DIGIT "." DIGIT
-- HTTP-name     = %s"HTTP"
def parseHttpVersionNumber : Parser (Nat × Nat) := do
  skipBytes "HTTP/".toUTF8
  let major ← uint8
  skipByte '.'.toUInt8
  let minor ← uint8
  pure ((major - 48 |>.toNat), (minor - 48 |>.toNat))

-- HTTP-version  = HTTP-name "/" DIGIT "." DIGIT
-- HTTP-name     = %s"HTTP"
def parseHttpVersion : Parser Version := do
  let (major, minor) ← parseHttpVersionNumber
  liftOption<| Version.ofNumber? major minor

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

/--
Parses the method token as text.
-/
def parseMethodToken : Parser String := do
  let raw ← token 16

  let methodToken ← liftOption<| String.fromUTF8? raw.toByteArray
  if methodToken.toList.any (fun c => c.toNat ≥ 'a'.toNat ∧ c.toNat ≤ 'z'.toNat) then
    fail "method token must be uppercase"
  else
    pure methodToken

def parseURI (limits : H1.Config) : Parser ByteArray := do
  let uri ← takeUntilUpTo (· == ' '.toUInt8) limits.maxUriLength
  return uri.toByteArray

/--
Parses a request line

request-line   = method SP request-target SP HTTP-version
-/
public def parseRequestLine (limits : H1.Config) : Parser Request.Head := do
  let method ← parseMethod <* sp
  let uri ← parseURI limits <* sp

  let uri ← match (Std.Http.URI.Parser.parseRequestTarget <* eof).run uri with
  | .ok res => pure res
  | .error res => fail res

  let (major, minor) ← parseHttpVersionNumber <* crlf
  if major == 1 ∧ minor == 1 then
    return ⟨method, .v11, uri, .empty⟩
  else
    fail "unsupported HTTP version"

/--
Parses a request line and returns the recognized HTTP method and version when available.

request-line = method SP request-target SP HTTP-version
-/
public def parseRequestLineRawVersion (limits : H1.Config) : Parser (Option Method × RequestTarget × Option Version) := do
  let methodToken ← parseMethodToken <* sp
  let uri ← parseURI limits <* sp

  let uri ← match (Std.Http.URI.Parser.parseRequestTarget <* eof).run uri with
  | .ok res => pure res
  | .error res => fail res

  let (major, minor) ← parseHttpVersionNumber <* crlf
  return (Method.ofString? methodToken, uri, Version.ofNumber? major minor)

-- field-line   = field-name ":" OWS field-value OWS
def parseFieldLine (limits : H1.Config) : Parser (String × String) := do
  let name ← token limits.maxHeaderNameLength
  let value ← skipByte ':'.toUInt8 *> ows limits *> optional (takeWhileUpTo isFieldVChar limits.maxHeaderValueLength) <* ows limits

  let name ← liftOption <| String.fromUTF8? name.toByteArray
  let value ← liftOption <| String.fromUTF8? <| value.map (·.toByteArray) |>.getD .empty
  let value := value.trimAsciiEnd.toString

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
partial def parseQuotedString (maxLength : Nat) : Parser String := do
  skipByte '"'.toUInt8

  let rec loop (buf : ByteArray) (length : Nat) : Parser ByteArray := do
    let b ← any

    if b == '"'.toUInt8 then
      return buf
    else if b == '\\'.toUInt8 then
      let next ← any
      if next == '\t'.toUInt8 ∨ next == ' '.toUInt8 ∨ isVChar next ∨ isObsChar next
        then
          let length := length + 1
          if length > maxLength then
            fail "quoted-string too long"
          else
            loop (buf.push next) length
        else fail s!"invalid quoted-pair byte: {Char.ofUInt8 next |>.quote}"
    else if isQdText b then
      let length := length + 1
      if length > maxLength then
        fail "quoted-string too long"
      else
        loop (buf.push b) length
    else
      fail s!"invalid qdtext byte: {Char.ofUInt8 b |>.quote}"

  liftOption <| String.fromUTF8? (← loop .empty 0)

-- chunk-ext = *( BWS ";" BWS chunk-ext-name [ BWS "=" BWS chunk-ext-val] )
def parseChunkExt (limits : H1.Config) : Parser (ExtensionName × Option String) := do
  ows limits *> skipByte ';'.toUInt8 *> ows limits
  let name ← (liftOption =<< String.fromUTF8? <$> ByteSlice.toByteArray <$> token limits.maxChunkExtNameLength) <* ows limits

  let some name := ExtensionName.ofString? name
    | fail "invalid extension name"

  if (← peekWhen? (· == '='.toUInt8)) |>.isSome then
    ows limits *> skipByte '='.toUInt8 *> ows limits
    let value ← ows limits *> (parseQuotedString limits.maxChunkExtValueLength <|> liftOption =<< (String.fromUTF8? <$> ByteSlice.toByteArray <$> token limits.maxChunkExtValueLength))

    return (name, some value)

  return (name, none)

/--
Parses the size and extensions of a chunk.
-/
public def parseChunkSize (limits : H1.Config) : Parser (Nat × Array (ExtensionName × Option String)) := do
  let size ← hex
  let ext ← manyItems (optional (attempt (parseChunkExt limits))) limits.maxChunkExtensions
  crlf
  return (size, ext)

/--
Result of parsing partial or complete information.
-/
public inductive TakeResult
  | complete (data : ByteSlice)
  | incomplete (data : ByteSlice) (remaining : Nat)

/--
Parses a single chunk in chunked transfer encoding.
-/
public def parseChunk (limits : H1.Config) : Parser (Option (Nat × Array (ExtensionName × Option String) × ByteSlice)) := do
  let (size, ext) ← parseChunkSize limits
  if size == 0 then
    return none
  else
    let data ← take size
    return some ⟨size, ext, data⟩

/--
Parses fixed-size data that can be incomplete.
-/
public def parseFixedSizeData (size : Nat) : Parser TakeResult := fun it =>
  if it.remainingBytes = 0 then
    .error it .eof
  else if it.remainingBytes < size then
    .success (it.forward it.remainingBytes) (.incomplete it.array[it.idx...(it.idx+it.remainingBytes)] (size - it.remainingBytes))
  else
    .success (it.forward size) (.complete (it.array[it.idx...(it.idx+size)]))

/--
Parses fixed-size chunk data that can be incomplete.
-/
public def parseChunkSizedData (size : Nat) : Parser TakeResult := do
  match ← parseFixedSizeData size with
  | .complete data => crlf *> return .complete data
  | .incomplete data res => return .incomplete data res

/--
Parses a trailer header (used after a chunked body).
-/
def parseTrailerHeader (limits : H1.Config) : Parser (Option (String × String)) := parseSingleHeader limits

/--
Parses trailer headers after a chunked body and returns them as an array of name-value pairs.

This is exposed for callers that need the trailer values directly (e.g. clients). The
internal protocol machine uses `parseLastChunkBody` instead, which discards trailer values.
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
  let bytes ← takeWhileUpTo (fun c => c != '\r'.toUInt8 ∧ c != '\n'.toUInt8) limits.maxReasonPhraseLength
  liftOption<| String.fromUTF8? bytes.toByteArray

/--
Parses a status line

status-line = HTTP-version SP status-code SP [ reason-phrase ]
-/
public def parseStatusLine (limits : H1.Config) : Parser Response.Head := do
  let (major, minor) ← parseHttpVersionNumber <* sp
  let status ← parseStatusCode <* sp
  let reasonPhrase ← parseReasonPhrase limits <* crlf
  if major == 1 ∧ minor == 1 then
    return {
      status
      reasonPhrase := some reasonPhrase
      version := .v11
      headers := .empty
    }
  else
    fail "unsupported HTTP version"

/--
Parses a status line and returns its reason phrase plus the recognized HTTP version if present in `Version`.

status-line = HTTP-version SP status-code SP [ reason-phrase ]
-/
public def parseStatusLineRawVersion (limits : H1.Config) : Parser (Status × String × Option Version) := do
  let (major, minor) ← parseHttpVersionNumber <* sp
  let status ← parseStatusCode <* sp
  let reasonPhrase ← parseReasonPhrase limits <* crlf
  return (status, reasonPhrase, Version.ofNumber? major minor)

/--
Parses the trailer section that follows the last chunk size line (`0\r\n`).
-/
public def parseLastChunkBody (limits : H1.Config) : Parser Unit := do
  discard <| manyItems (parseTrailerHeader limits) limits.maxTrailerHeaders
  crlf

end Std.Http.Protocol.H1
