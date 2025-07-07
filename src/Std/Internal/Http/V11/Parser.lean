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
namespace Internal
namespace Http
namespace V11
namespace Parser

syntax "b!" char : term

def failNone (x : Option α) : Parser α :=
  if let some res := x then
    pure res
  else
    fail "expected value but got none"

def toLowerFast (c : UInt8) : UInt8 :=
  if c >= 'A'.toUInt8 && c <= 'Z'.toUInt8 then
    c ||| 0x20
  else
    c

def _root_.ByteArray.toLowerCase (x : ByteArray) : ByteArray :=
  ByteArray.mk (x.data.map toLowerFast)

deriving instance Repr for ByteArray

macro_rules
  | `(b!$lit) => do
    let char := lit.getChar
    if char.val > 255 then Lean.Macro.throwErrorAt lit "Invalid character"
    return Lean.Syntax.mkNumLit (toString char.val)

structure RequestLine where
  method : ByteArray
  uri : ByteArray
  major : UInt8
  minor : UInt8
deriving Repr

structure StatusLine where
  major : UInt8
  minor : UInt8
  statusCode : Nat
  reasonPhrase : ByteArray
deriving Repr

structure Header where
  name : String
  value : String
deriving Repr

inductive HttpType
  | request
  | response
deriving Inhabited, Repr

inductive StartLine : Type
  | request : RequestLine → StartLine
  | response : StatusLine → StartLine
deriving Repr

structure HttpMessage where
  firstLine : StartLine
  headers : Array Header

def isTokenCharacter (c : UInt8) : Bool :=
    c > 31 && c != '('.toUInt8 && c != ')'.toUInt8 && c != '<'.toUInt8 && c != '>'.toUInt8 &&
    c != '@'.toUInt8 && c != ','.toUInt8 && c != ';'.toUInt8 && c != ':'.toUInt8 &&
    c != '"'.toUInt8 && c != '/'.toUInt8 && c != '['.toUInt8 && c != ']'.toUInt8 &&
    c != '?'.toUInt8 && c != '='.toUInt8 && c != '{'.toUInt8 && c != '}'.toUInt8 && c != ' '.toUInt8

def parseRequestLine : Parser RequestLine := do
  let method ← takeWhile isTokenCharacter
  skipByte ' '.toUInt8
  let uri ← takeUntil (· == ' '.toUInt8)
  skipBytes " HTTP/".toUTF8
  let major ← digit
  skipByte '.'.toUInt8
  let minor ← digit
  skipBytes "\r\n".toUTF8
  return ⟨method, uri, major.toUInt8, minor.toUInt8⟩

def parseStatusLine : Parser StatusLine := do
  skipBytes "HTTP/".toUTF8
  let major ← digit
  skipByte '.'.toUInt8
  let minor ← digit
  skipByte ' '.toUInt8
  let d1 ← digit
  let d2 ← digit
  let d3 ← digit
  let statusCode := (d1.toUInt8 - '0'.toUInt8).toNat * 100 + (d2.toUInt8 - '0'.toUInt8).toNat * 10 + (d3.toUInt8 - '0'.toUInt8).toNat
  skipByte ' '.toUInt8
  let reasonPhrase ← takeUntil (· == '\r'.toUInt8)
  skipBytes "\r\n".toUTF8
  return ⟨major.toUInt8, minor.toUInt8, statusCode, reasonPhrase⟩

def parseHeader : Parser (Option Header) := do
  if (← optional (skipBytes "\r\n".toUTF8)).isSome then
    return none
  else
    let name ← takeUntil (· == ':'.toUInt8)
    skipByte ':'.toUInt8
    skipWhile (· == ' '.toUInt8)
    let value ← takeUntil (· == '\r'.toUInt8)
    skipBytes "\r\n".toUTF8
    return some ⟨← failNone (String.fromUTF8? name), ← failNone (String.fromUTF8? value)⟩

def parseHexDigit : Parser UInt8 := do
  let b ← any
  if b ≥ '0'.toUInt8 && b ≤ '9'.toUInt8 then return b - '0'.toUInt8
  else if b ≥ 'A'.toUInt8 && b ≤ 'F'.toUInt8 then return b - 'A'.toUInt8 + 10
  else if b ≥ 'a'.toUInt8 && b ≤ 'f'.toUInt8 then return b - 'a'.toUInt8 + 10
  else fail s!"Invalid hex digit {Char.ofUInt8 b |>.quote}"

def parseHex : Parser Nat := do
  let hexDigits ← many1 (attempt parseHexDigit)
  return (hexDigits.foldl (fun acc cur => acc * 16 + cur.toNat) 0)

def parseChunkExt : Parser (Option ByteArray) := do
  if (← optional (skipByte ';'.toUInt8)).isSome then
    some <$> takeUntil (· == '\r'.toUInt8)
  else
    return none

def parseChunkSize : Parser (Nat × Option ByteArray) := do
  let size ← parseHex
  let ext ← parseChunkExt
  skipBytes "\r\n".toUTF8
  return (size, ext)

def parseChunkData (size : Nat) : Parser ByteArray := do
  let res ← take size
  skipBytes "\r\n".toUTF8
  return res

def parseFixedBody (size : Nat)  : Parser ByteArray :=
  take size

def findHeader (headers : Array Header) (name : String) : Option String :=
  let nameBytes := name.toLower
  headers.find? (fun h => h.name.toLower == nameBytes) |>.map (·.value)

def isChunkedEncoding (headers : Array Header) : Bool :=
  match findHeader headers "Transfer-Encoding" with
  | some value =>
    value.toLower == "chunked"
  | none => false

def getContentLength (headers : Array Header) : Option Nat :=
  match findHeader headers "Content-Length" with
  | some value => String.toNat? value
  | none => none

def shouldHaveBody (firstLine : StartLine) (headers : Array Header) : Bool :=
  match firstLine with
  | .response statusLine =>
    statusLine.statusCode ≥ 200
    && statusLine.statusCode ≠ 204
    && statusLine.statusCode ≠ 304
  | .request _ =>
    isChunkedEncoding headers || (getContentLength headers |>.isSome)

def parseFirstLine : Parser StartLine := do
  let peek ← peekWhen? (· == 'H'.toUInt8)
  if peek.isSome
    then return .response (← parseStatusLine)
    else return .request (← parseRequestLine)

inductive HttpState (t : Type) : Type
  | needFirstLine : HttpState t
  | needHeader : t → HttpState t
  | needChunkedSize : HttpState t
  | needChunkedBody : Nat → Option ByteArray → HttpState t
  | needFixedBody : Nat → HttpState t
  | needData : HttpState t → HttpState t
  | complete : HttpState t
  | receiveRequest : RequestLine → HttpState t → HttpState t
  | receiveResponse : StatusLine → HttpState t → HttpState t
  | receivedData (data : ByteArray) (next : HttpState t) : HttpState t
  | failed (s : String) : HttpState t
deriving Inhabited

inductive State
  | receiving
  | idle
  | sendingData

structure HttpConnection (t : Type) where
  state : HttpState t := .needFirstLine
  headers : Array Header := #[]
  buffer : ByteArray.Iterator := .mk .empty 0
  sendBuffer : Array ByteArray := #[]
deriving Inhabited

namespace HttpConnection

/-
def stepRequest (parser : HttpConnection RequestLine) (input : ByteArray) : HttpConnection RequestLine :=
  let buffer := parser.buffer.array.extract parser.buffer.idx parser.buffer.array.size
  let buffer := buffer ++ input
  let buffer := buffer.iter

  match parser.state with
  | .needFirstLine =>
    match parseFirstLine buffer with
    | .success buffer (.request res) => { parser with buffer, state := .receiveRequest res (.needHeader (.request res)) }
    | .success buffer (.response res) => { parser with buffer, state := .receiveResponse res (.needHeader (.response res)) }
    | .error _ .eof => { parser with buffer, state := .needData parser.state }
    | .error _ other => { parser with buffer, state := .failed (toString other) }
  | .needHeader startLine =>
    match parseHeader buffer with
    | .success buffer none =>
      if shouldHaveBody startLine parser.headers then
        if isChunkedEncoding parser.headers then
          { parser with buffer, state := .needChunkedSize }
        else
          match getContentLength parser.headers with
          | some length => { parser with buffer, state := .needFixedBody length }
          | none => { parser with buffer, state := .failed "Missing Content-Length for non-chunked body" }
      else
        { parser with state := .complete, buffer, headers := #[] }
    | .success buffer (some res) => { parser with buffer, headers := parser.headers.push res }
    | .error _ .eof => { parser with buffer, state := .needData parser.state }
    | .error _ err => { parser with buffer, state := .failed (toString err) }
  | .needChunkedSize =>
    match parseChunkSize buffer with
    | .success buffer (size, ext) =>
      if size == 0
        then { parser with buffer, state := .complete }
        else { parser with buffer, state := .needChunkedBody size ext }
    | .error _ .eof => { parser with buffer, state := .needData parser.state }
    | .error _ err => { parser with buffer, state := .failed (toString err) }
  | .needChunkedBody size _ =>
    match parseChunkData size buffer with
    | .success buffer body => { parser with buffer, state := .receivedData body .needChunkedSize }
    | .error _ .eof => { parser with buffer, state := .needData parser.state }
    | .error _ err => { parser with buffer, state := .failed (toString err) }
  | .needFixedBody length =>
    match parseFixedBody length buffer with
    | .success buffer body => { parser with state := .receivedData body .complete, buffer }
    | .error _ .eof => { parser with buffer, state := .needData parser.state }
    | .error _ err => { parser with buffer, state := .failed (toString err) }
  | _ => { parser with buffer }
-/
