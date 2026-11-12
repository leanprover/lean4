/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Parsec
public import Std.Http.Data
public import Std.Internal.Parsec.ByteArray
public import Std.Http.Protocol.H1.Config
import Init.Data.String.Lossy

/-!
This module defines parsers for HTTP/1.1 request and response lines, headers, and body framing. The
reference used is https://httpwg.org/specs/rfc9112.html.
-/

namespace Std.Http.Protocol.H1

open Std Std.Internal Parsec ByteArray Internal.Char

set_option linter.all true

/--
Checks if a byte is `field-content`, `HTAB / SP / VCHAR / obs-text`: the bytes of a field value and
of a reason phrase.
-/
@[inline]
def isFieldContentByte (c : UInt8) : Bool :=
  fieldContent (Char.ofUInt8 c)

/--
Checks if a byte may appear unescaped inside a quoted-string value.

Allows `HTAB / SP / %x21 / %x23-5B / %x5D-7E` (strict ASCII-only; no obs-text).
-/
@[inline]
def isQdText (c : UInt8) : Bool :=
  qdtext (Char.ofUInt8 c)

/--
Checks if a byte is optional whitespace (`OWS = SP / HTAB`, RFC 9110 §5.6.3).
-/
@[inline]
def isOwsByte (c : UInt8) : Bool :=
  ows (Char.ofUInt8 c)

-- Parser blocks

/--
Like `optional (attempt p)`, but an `.eof` failure of `p` is propagated instead of becoming `none`.

The protocol machine treats `.eof` as "need more data". If an item is cut off by the end of the
currently buffered input, swallowing the `.eof` would backtrack and let the next parser fail on the
unfinished item's bytes, turning a valid message into a hard parse error.
-/
@[inline]
def optionalUnlessEof (p : Parser α) : Parser (Option α) := fun it =>
  match p it with
  | .success rem res => .success rem (some res)
  | .error rem .eof => .error rem .eof
  | .error _ _ => .success it none

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
def parseToken (limit : Nat) : Parser ByteSlice :=
  takeWhileUpTo1 (fun c => tchar (Char.ofUInt8 c)) limit

/--
Parses a line terminator.
-/
@[inline]
def crlf : Parser Unit := do
  skipBytes "\r\n".toUTF8

/--
Consumes and ignores empty lines (`CRLF`) that appear before a request-line.

https://httpwg.org/specs/rfc9112.html#rfc.section.2.2:

"In the interest of robustness, a server that is expecting to receive and parse a request-line SHOULD
ignore at least one empty line (CRLF) received prior to the request-line."
-/
def skipLeadingRequestEmptyLines (limits : H1.Config) : Parser Unit := do
  let mut count := 0
  while (← peekWhen? (· == '\r'.toUInt8)).isSome do
    if count >= limits.maxLeadingEmptyLines then
      fail "too many leading empty lines"
    crlf
    count := count + 1

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
  discard <| takeWhileUpTo isOwsByte limits.maxSpaceSequence

  if (← peekWhen? isOwsByte) |>.isSome then
    fail "invalid space sequence"
  else
    pure ()

/--
The value of an ASCII hex digit (`isHexDigitByte`).
-/
@[inline]
def hexValue (b : UInt8) : Nat :=
  if b ≤ '9'.toUInt8 then (b - '0'.toUInt8).toNat
  else if b ≤ 'F'.toUInt8 then (b - 'A'.toUInt8 + 10).toNat
  else (b - 'a'.toUInt8 + 10).toNat

/--
Parses a hexadecimal integer (one or more hex digits, up to 16 after any leading zeros, which do not
change the value).
Used for chunk-size lines in chunked transfer encoding.
-/
def hex : Parser Nat := do
  let zeros ← takeWhile (· == '0'.toUInt8)
  let digits ← takeWhileUpTo isHexDigitByte 17
  if digits.size > 16 then
    fail "chunk size too large"
  if zeros.size == 0 && digits.size == 0 then
    fail "expected hex digit"
  return digits.byteArray.foldl (fun n b => n * 16 + hexValue b) 0 digits.start digits.stop

-- Actual parsers

/--
Parses `HTTP-version = HTTP-name "/" DIGIT "." DIGIT`. A higher minor version of HTTP/1 is read as
HTTP/1.1 (RFC 9110 §2.5, §6.2). Returns `none` for a version this library does not know.
-/
def parseHttpVersion : Parser (Option Version) := do
  skipBytes "HTTP/".toUTF8
  let major := (← digit).toNat - 48
  skipByte '.'.toUInt8
  let minor := (← digit).toNat - 48
  return Version.ofNumber? major (if major == 1 then min minor 1 else minor)

/--
Accepts HTTP/1.0 and HTTP/1.1, the versions an HTTP/1 message can have.
-/
def http1Version : Option Version → Parser Version
  | some .v10 => pure .v10
  | some .v11 => pure .v11
  | _ => fail "unsupported HTTP version"

/--
The methods `parseMethod` recognizes, by name, the most common first: every `Method`
(`Method.all_complete`).
-/
def knownMethods : Array (ByteSlice × Method) :=
  Method.all.map fun method => ((toString method).toUTF8.toByteSlice, method)

/-
method         = token

The whole token is read before it is looked up, so a read that ends inside a method name waits for
more input instead of matching a shorter method (`UPDATE` inside `UPDATEREDIRECTREF`), and a
method that only starts with a known one (`GETX`) is not read as it.

A token the server does not recognize fails with `"unrecognized method"` when it is followed by the
space that ends a method, or by more token bytes past the 64-byte limit: RFC 9110 §9.1 and RFC 9112
§3 answer such a method with 501. A token followed by any other byte fails with `"invalid method"`.
-/
def parseMethod : Parser Method := do
  let token ← parseToken 64
  match knownMethods.find? fun (name, _) => name.size == token.size && name == token with
  | some (_, method) => return method
  | none =>
    let next ← peek!
    if next == ' '.toUInt8 || tchar (Char.ofUInt8 next) then fail "unrecognized method"
    else fail "invalid method"

/--
Parses a request-target URI, up to `limits.maxUriLength` bytes.
Fails with `"uri too long"` if the target exceeds the configured limit.

The target ends at SP, or at CR or LF, which no target contains: a request line with no version
then fails at once on the missing SP, instead of waiting for one (RFC 9112 §3).
-/
def parseURI (limits : H1.Config) : Parser ByteArray := do
  let endsTarget (c : UInt8) := c == ' '.toUInt8 || c == '\r'.toUInt8 || c == '\n'.toUInt8
  let uri ← takeUntilUpTo endsTarget limits.maxUriLength
  if uri.size == limits.maxUriLength then
    if (← peekWhen? (!endsTarget ·)) |>.isSome then
      fail "uri too long"

  return uri.toByteArray

/--
The URI limits for a request-target. `maxUriLength` bounds the whole target, so no component limit
lower than it rejects a target the server accepts as a whole, which RFC 9112 §3 would answer with
`414`, not `400`. The host keeps its own limit, the length of a DNS name.
-/
def requestTargetConfig (limits : H1.Config) : URI.Config :=
  let n := limits.maxUriLength
  { maxSchemeLength := n, maxUserInfoLength := n, maxSegmentLength := n, maxQueryLength := n,
    maxFragmentLength := n, maxPathSegments := n, maxTotalPathLength := n, maxQueryParams := n }

/--
Parses a request line and returns the method, the target and the version, `none` for a version this
library does not know.

request-line = method SP request-target SP HTTP-version
-/
public def parseRequestLineRawVersion (limits : H1.Config) :
    Parser (Method × RequestTarget × Option Version) := do
  skipLeadingRequestEmptyLines limits
  let method ← parseMethod <* sp
  let rawUri ← parseURI limits <* sp
  let uri ← match (Std.Http.URI.Parser.parseRequestTarget (requestTargetConfig limits) <* eof).run rawUri with
  | .ok res => pure res
  | .error res => fail res
  let version ← parseHttpVersion <* crlf
  return (method, uri, version)

/--
Parses a request line of HTTP/1.0 or HTTP/1.1 and returns a fully-typed `Request.Head`.
-/
public def parseRequestLine (limits : H1.Config) : Parser Request.Head := do
  let (method, uri, version) ← parseRequestLineRawVersion limits
  return ⟨method, ← http1Version version, uri, .empty⟩

/--
Parses a single header field line.

`field-line = field-name ":" OWS field-value OWS`
-/
def parseFieldLine (limits : H1.Config) : Parser (String × String) := do
  let name ← parseToken limits.maxHeaderNameLength
  let value ← skipByte ':'.toUInt8 *> ows limits *> optional (takeWhileUpTo isFieldContentByte limits.maxHeaderValueLength) <* ows limits

  let name ← liftOption <| String.fromUTF8? name.toByteArray
  -- obs-text need not be UTF-8; it is kept as opaque data, with any invalid sequence replaced.
  let value := String.fromUTF8Lossy <| value.map (·.toByteArray) |>.getD .empty
  let value := value.trimAsciiEnd.toString

  return (name, value)

/--
Parses a single header field line, or returns `none` when it sees the blank line that
terminates the header section.

```
field-line = field-name ":" OWS field-value OWS CRLF
```
-/
public def parseSingleHeader (limits : H1.Config) : Parser (Option (String × String)) := do
  let next ← peek?
  if next == some '\r'.toUInt8 ∨ next == some '\n'.toUInt8 then
    crlf
    pure none
  else
    some <$> (parseFieldLine limits <* crlf)

/--
Parses the line that continues a field value after an obsolete line folding (`obs-fold = OWS CRLF
RWS`, RFC 9112 §5.2): the leading whitespace, the field content and the terminating CRLF. Returns the
content without the whitespace around it.
-/
public def parseObsFoldContinuation (limits : H1.Config) : Parser String := do
  let value ← ows limits *> optional (takeWhileUpTo isFieldContentByte limits.maxHeaderValueLength) <* crlf
  let value := String.fromUTF8Lossy <| value.map (·.toByteArray) |>.getD .empty
  return value.trimAscii.toString

/--
Parses a quoted-string value, unescaping quoted-pairs, and returns its bytes.

`quoted-string = DQUOTE *( qdtext / quoted-pair ) DQUOTE`, where both `qdtext` and `quoted-pair`
also allow obs-text (`%x80-FF`, RFC 9110 §5.6.4).
-/
def parseQuotedString (maxLength : Nat) : Parser ByteArray := do
  skipByte '"'.toUInt8
  loop .empty 0
where
  loop (buf : ByteArray) (length : Nat) : Parser ByteArray := do
    let b ← any

    if b == '"'.toUInt8 then
      return buf
    else if b == '\\'.toUInt8 then
      let next ← any
      if quotedPairChar (Char.ofUInt8 next) || next ≥ 0x80
        then
          if length + 1 > maxLength then
            fail "quoted-string too long"
          else
            loop (buf.push next) (length + 1)
        else fail s!"invalid quoted-pair byte: {Char.ofUInt8 next |>.quote}"
    else if isQdText b || b ≥ 0x80 then
      if length + 1 > maxLength then
        fail "quoted-string too long"
      else
        loop (buf.push b) (length + 1)
    else
      fail s!"invalid qdtext byte: {Char.ofUInt8 b |>.quote}"
  termination_by maxLength - length

/--
Parses one chunk extension:
`chunk-ext = *( BWS ";" BWS chunk-ext-name [ BWS "=" BWS chunk-ext-val] )`.

Returns `none` for an extension whose quoted value holds obs-text, which `Chunk.ExtensionValue` cannot
represent: such an extension is ignored, as a recipient ignores any extension it does not
recognize (RFC 9112 §7.1.1).
-/
def parseChunkExt (limits : H1.Config) :
    Parser (Option (Chunk.ExtensionName × Option Chunk.ExtensionValue)) := do
  ows limits *> skipByte ';'.toUInt8 *> ows limits
  let name ← (liftOption =<< String.fromUTF8? <$> ByteSlice.toByteArray <$> parseToken limits.maxChunkExtNameLength) <* ows limits

  let some name := Chunk.ExtensionName.ofString? name
    | fail "invalid extension name"

  if (← peekWhen? (· == '='.toUInt8)) |>.isSome then
    -- RFC 9112 §7.1.1: BWS is allowed around "=".
    -- The `<* ows limits` after the name already consumed any trailing whitespace,
    -- so these ows calls are no-ops in practice, but kept for explicit grammar correspondence.
    ows limits *> skipByte '='.toUInt8 *> ows limits
    if (← peekWhen? (· == '"'.toUInt8)).isSome then
      let bytes ← parseQuotedString limits.maxChunkExtValueLength
      return (String.fromUTF8? bytes >>= Chunk.ExtensionValue.ofString?).map (name, some ·)

    let value ← liftOption =<< (String.fromUTF8? <$> ByteSlice.toByteArray <$> parseToken limits.maxChunkExtValueLength)
    let some value := Chunk.ExtensionValue.ofString? value
      | fail "invalid extension value"

    return some (name, some value)

  return some (name, none)

/--
Parses the size and extensions of a chunk.
-/
public def parseChunkSize (limits : H1.Config) : Parser (Nat × Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) := do
  let size ← hex
  let ext ← extensions #[] 0
  crlf
  return (size, ext)
where
  /--
  Parses the extensions after the `count` ones already read. One cut off by the end of the input
  fails with `.eof`, so it is parsed again once the rest arrives.
  -/
  extensions (acc : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (count : Nat) :
      Parser (Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) := do
    let some ext ← optionalUnlessEof (parseChunkExt limits) | return acc
    if h : count + 1 > limits.maxChunkExtensions then
      fail s!"too many chunk extensions: {count + 1} > {limits.maxChunkExtensions}"
    else
      extensions (ext.elim acc acc.push) (count + 1)
  termination_by limits.maxChunkExtensions - count

/--
Whether `name` (compared case-insensitively) is a field a trailer section must not carry (RFC 9112
§6.5). The fields that frame or route a message (`content-length`, `transfer-encoding`, `host`,
`connection`, `te`, `upgrade`, `trailer`) always are: in a trailer section such a field is an
attempt to reframe the message after the fact, which a downstream proxy might act on. With
`strict`, so are the fields that control how the message is processed (`expect`, `authorization`,
`max-forwards`, `cache-control`, `content-encoding`).
-/
def isRejectedTrailerField (strict : Bool) (name : String) : Bool :=
  let n := name.toLower
  n == "content-length" || n == "transfer-encoding" || n == "host" || n == "connection" ||
    n == "te" || n == "upgrade" || n == "trailer" ||
    strict && (n == "expect" || n == "authorization" || n == "max-forwards" ||
      n == "cache-control" || n == "content-encoding")

/--
Parses a trailer header (used after a chunked body), rejecting a field a trailer section must not
carry (`isRejectedTrailerField`). Without `strict`, only framing and routing fields are rejected; the
others are parsed and left for the caller to drop, since RFC 9110 §6.5.1 asks recipients not to
merge them rather than to reject a message that is otherwise complete.
-/
public def parseTrailerHeader (limits : H1.Config) (strict : Bool := true) :
    Parser (Option (String × String)) := do
  let result ← parseSingleHeader limits
  if let some (name, _) := result then
    if isRejectedTrailerField strict name then
      fail s!"forbidden trailer field: {name}"
  return result

/--
Parses a reason phrase (text after status code).

Allows `HTAB / SP / VCHAR / obs-text` bytes. A client ignores the phrase (RFC 9112 §4), so bytes
that are not UTF-8 are replaced rather than rejected.
-/
def parseReasonPhrase (limits : H1.Config) : Parser String := do
  let bytes ← takeWhileUpTo isFieldContentByte limits.maxReasonPhraseLength
  return String.fromUTF8Lossy bytes.toByteArray

/--
Parses a status-code (3 decimal digits), the following reason phrase, and the
terminating CRLF; returns a typed `Status`.

A code of 000–099 is a well-formed `3DIGIT` that `Status` cannot hold. RFC 9110 §15 asks a client to
process such a response as a 5xx, so it is read as `500 Internal Server Error`.
-/
def parseStatusCode (limits : H1.Config) : Parser Status := do
  let d1 ← digit
  let d2 ← digit
  let d3 ← digit
  let code := (d1.toNat - 48) * 100 + (d2.toNat - 48) * 10 + (d3.toNat - 48)
  -- Servers that send no reason phrase often leave out the space before it too.
  let phrase := (← optional (sp *> parseReasonPhrase limits)).getD ""
  crlf

  if code < 100 then
    return .internalServerError

  if h : IsValidReasonPhrase phrase then
    if let some status := Status.ofCode (some ⟨phrase, h⟩) code.toUInt16 then
      return status

  fail "invalid status code"

/--
Parses a status line and returns the status code and the version, `none` for a version this library
does not know. Consumes and discards the reason phrase.

status-line = HTTP-version SP status-code SP [ reason-phrase ] CRLF
-/
public def parseStatusLineRawVersion (limits : H1.Config) : Parser (Status × Option Version) := do
  let version ← parseHttpVersion <* sp
  let status ← parseStatusCode limits
  return (status, version)

/--
Parses a status line of HTTP/1.0 or HTTP/1.1 and returns a fully-typed `Response.Head`.
-/
public def parseStatusLine (limits : H1.Config) : Parser Response.Head := do
  let (status, version) ← parseStatusLineRawVersion limits
  return { status, version := ← http1Version version, headers := .empty }

end Std.Http.Protocol.H1
