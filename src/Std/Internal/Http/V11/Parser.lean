/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init.Data
import Std.Internal.Parsec
import Std.Internal.Parsec.ByteArray

open Std Internal Parsec ByteArray

namespace Std
namespace Http
namespace V11
namespace Parser

def failNone (x : Option α) : Parser α :=
  if let some res := x then
    pure res
  else
    fail "expected value but got none"

deriving instance Repr for ByteArray

instance : Repr ByteSlice where
  reprPrec x := reprPrec x.toByteArray

instance : Inhabited ByteSlice where
  default := ⟨.empty, 0, 0, by simp⟩

/--
Structure representing an HTTP request line
-/
structure RequestLine where
  method : ByteSlice
  uri : ByteSlice
  major : UInt8
  minor : UInt8
deriving Repr, Inhabited

/--
Structure representing an HTTP status line
-/
structure StatusLine where
  major : UInt8
  minor : UInt8
  statusCode : Nat
  reasonPhrase : ByteSlice
deriving Repr

/--
Structure representing an HTTP header
-/
structure Header where
  name : String
  value : String
deriving Repr

/--
Enumeration for HTTP message types
-/
inductive HttpType
  | request
  | response
deriving Inhabited, Repr

/--
Union type for HTTP start lines (request or response)
-/
inductive StartLine : Type
  | request : RequestLine → StartLine
  | response : StatusLine → StartLine
deriving Repr

/--
Structure representing a complete HTTP message
-/
structure HttpMessage where
  firstLine : StartLine
  headers : Array Header

/--
Structure representing a chunked transfer encoding chunk
-/
structure Chunk where
  size : Nat
  extension : Option ByteSlice
  data : ByteSlice
deriving Repr

/--
Enumeration for different HTTP body types
-/
inductive HttpBody
  | fixed : ByteSlice → HttpBody
  | chunked : Array Chunk → Array Header → HttpBody
  | none : HttpBody
deriving Repr

/--
Complete HTTP message with body
-/
structure CompleteHttpMessage where
  firstLine : StartLine
  headers : Array Header
  body : HttpBody
deriving Repr

/--
This function checks if a character is a valid token character according to HTTP spec
-/
def isTokenCharacter (c : UInt8) : Bool :=
  c > 31 && c != '('.toUInt8 && c != ')'.toUInt8 && c != '<'.toUInt8 && c != '>'.toUInt8 &&
  c != '@'.toUInt8 && c != ','.toUInt8 && c != ';'.toUInt8 && c != ':'.toUInt8 &&
  c != '"'.toUInt8 && c != '/'.toUInt8 && c != '['.toUInt8 && c != ']'.toUInt8 &&
  c != '?'.toUInt8 && c != '='.toUInt8 && c != '{'.toUInt8 && c != '}'.toUInt8 && c != ' '.toUInt8

/--
This function parses CRLF sequence
-/
def parseCRLF : Parser Unit :=
  skipBytes "\r\n".toUTF8

/--
This function parses a sequence of digits and converts to UInt8
-/
def parseDigitAsUInt8 : Parser UInt8 := do
  let d ← digit
  return d.toUInt8

/--
This function parses HTTP version (major.minor)
-/
def parseHttpVersion : Parser (UInt8 × UInt8) := do
  let major ← parseDigitAsUInt8
  skipByte '.'.toUInt8
  let minor ← parseDigitAsUInt8
  return (major, minor)

/--
This function parses a 3-digit status code
-/
def parseStatusCode : Parser Nat := do
  let d1 ← digit
  let d2 ← digit
  let d3 ← digit
  return (d1.toUInt8 - '0'.toUInt8).toNat * 100 + (d2.toUInt8 - '0'.toUInt8).toNat * 10 + (d3.toUInt8 - '0'.toUInt8).toNat

/--
This function parses an HTTP request line
-/
def parseRequestLine : Parser RequestLine := do
  let method ← takeWhile isTokenCharacter
  skipByte ' '.toUInt8
  let uri ← takeUntil (· == ' '.toUInt8)
  skipBytes " HTTP/".toUTF8
  let (major, minor) ← parseHttpVersion
  parseCRLF
  return ⟨method, uri, major, minor⟩

/--
This function parses an HTTP status line
-/
def parseStatusLine : Parser StatusLine := do
  skipBytes "HTTP/".toUTF8
  let (major, minor) ← parseHttpVersion
  skipByte ' '.toUInt8
  let statusCode ← parseStatusCode
  skipByte ' '.toUInt8
  let reasonPhrase ← takeUntil (· == '\r'.toUInt8)
  parseCRLF
  return ⟨major, minor, statusCode, reasonPhrase⟩

/--
This function parses a header name-value pair
-/
def parseHeaderLine : Parser Header := do
  let name ← takeUntil (· == ':'.toUInt8)
  skipByte ':'.toUInt8
  skipWhile (· == ' '.toUInt8)
  let value ← takeUntil (· == '\r'.toUInt8)
  parseCRLF
  return ⟨← failNone (String.fromUTF8? name.toByteArray), ← failNone (String.fromUTF8? value.toByteArray)⟩

/--
This function parses a single HTTP header or returns none if end of headers is reached
-/
def parseHeader : Parser (Option Header) := do
  if (← optional parseCRLF).isSome then
    return none
  else
    some <$> parseHeaderLine

/--
This function parses a hexadecimal digit
-/
def parseHexDigit : Parser UInt8 := do
  let b ← any
  if b ≥ '0'.toUInt8 && b ≤ '9'.toUInt8 then return b - '0'.toUInt8
  else if b ≥ 'A'.toUInt8 && b ≤ 'F'.toUInt8 then return b - 'A'.toUInt8 + 10
  else if b ≥ 'a'.toUInt8 && b ≤ 'f'.toUInt8 then return b - 'a'.toUInt8 + 10
  else fail s!"Invalid hex digit {Char.ofUInt8 b |>.quote}"

/--
This function parses a hexadecimal number
-/
def parseHex : Parser Nat := do
  let hexDigits ← many1 (attempt parseHexDigit)
  return (hexDigits.foldl (fun acc cur => acc * 16 + cur.toNat) 0)

/--
This function parses chunk extensions
-/
def parseChunkExt : Parser (Option ByteSlice) := do
  if (← optional (skipByte ';'.toUInt8)).isSome then
    some <$> takeUntil (· == '\r'.toUInt8)
  else
    return none

/--
This function parses the size and extension of a chunk
-/
def parseChunkSize : Parser (Nat × Option ByteSlice) := do
  let size ← parseHex
  let ext ← parseChunkExt
  parseCRLF
  return (size, ext)

/--
This function parses chunk data of a specific size
-/
def parseChunkData (size : Nat) : Parser ByteSlice := do
  let res ← take size
  parseCRLF
  return res

/--
This function parses a trailer header (used after chunked body)
-/
def parseTrailerHeader : Parser (Option Header) := parseHeader

/--
This function parses a fixed-length body
-/
def parseFixedBody (size : Nat) : Parser ByteSlice :=
  take size

/--
This function parses the first line of an HTTP message (request or response)
-/
def parseFirstLine : Parser StartLine := do
  let peek ← peekWhen? (· == 'H'.toUInt8)
  if peek.isSome
    then return .response (← parseStatusLine)
    else return .request (← parseRequestLine)

/--
This function parses multiple items until a terminator is found
-/
def parseMany {α : Type} (parser : Parser (Option α)) : Parser (Array α) := do
  let items ← many (parser.bind (fun item => match item with
    | some x => return x
    | none => fail "End of items"))
  return items

/--
This function parses all HTTP headers until the end marker
-/
def parseHeaders : Parser (Array Header) := do
  let headers ← parseMany parseHeader
  parseCRLF
  return headers

/--
This function parses a single chunk in chunked transfer encoding
-/
def parseChunk : Parser (Option Chunk) := do
  let (size, ext) ← parseChunkSize
  if size == 0 then
    return none
  else
    let data ← parseChunkData size
    return some ⟨size, ext, data⟩

/--
This function parses all chunks in chunked transfer encoding
-/
def parseChunks : Parser (Array Chunk) :=
  parseMany parseChunk

/--
This function parses trailer headers after chunked body
-/
def parseTrailers : Parser (Array Header) := do
  let trailers ← parseMany parseTrailerHeader
  parseCRLF
  return trailers
