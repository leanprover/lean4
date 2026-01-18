/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Http.Data.Header.Name
public import Std.Internal.Http.Data.URI
public section

/-!
# Header

This module defines the `Header` typeclass and common HTTP header types. It provides a type-safe way
to work with HTTP headers while maintaining their semantic meaning and validation rules.
-/

namespace Std.Http

set_option linter.all true

/--
Typeclass for HTTP headers that associates a header name with a type and provides conversion to/from header values.
-/
class Header (α : Type) where
  /--
  The canonical name of this header
  -/
  name : α → Header.Name

  /--
  Converts a value of type α to a validated header value
  -/
  value : α → Header.Value

  /--
  Attempts to parse a header value into type α given the header name
  -/
  parse : Header.Name → Header.Value → Option α

namespace Header

/--
Represents the Content-Length header, which indicates the size of the message body in bytes.
-/
structure ContentLength where
  /--
  The size of the content in bytes
  -/
  size : Nat
deriving BEq, DecidableEq, Repr

namespace ContentLength

instance : Inhabited ContentLength :=
  ⟨⟨0⟩⟩

/--
Creates a ContentLength from a natural number.
-/
@[inline]
def new (n : Nat) : ContentLength :=
  ⟨n⟩

/--
Attempts to parse a ContentLength from a string.
-/
def ofString? (s : String) : Option ContentLength :=
  s.trimAscii.toNat?.map new

/--
Creates a ContentLength from a string, panicking if invalid.
-/
def ofString! (s : String) : ContentLength :=
  match ofString? s with
  | some cl => cl
  | none => panic! s!"invalid content-length: {s.quote}"

instance : ToString ContentLength where
  toString cl := toString cl.size

end ContentLength

instance : Header ContentLength where
  name _ := .new "content-length"
  value cl := .ofString! (toString cl.size)
  parse _ v := ContentLength.ofString? v.value

/--
Validates that "chunked" encoding, if present, appears exactly once and is last.
-/
abbrev IsValidTransferEncoding (encodings : Array String) : Prop :=
  if encodings.isEmpty then
    False
  else
    let chunkedIndices := encodings.mapIdx (·,·) |>.filter (fun (_, enc) => enc == "chunked")
    let chunkedCount := chunkedIndices.size
    let lastIsChunked := encodings.back? == some "chunked"

    if chunkedCount > 1 then
      False
    else if chunkedCount = 1 && !lastIsChunked then
      False
    else
      True

/--
Represents the Transfer-Encoding header, which specifies the encoding transformations
applied to the message body.
-/
structure TransferEncoding where
  /--
  The list of encoding transformations in order
  -/
  encodings : Array String

  /--
  Proof that the encodings are valid according to HTTP/1.1 spec.
  This ensures "chunked" appears at most once and only as the last encoding.
  -/
  validity : IsValidTransferEncoding encodings

deriving BEq, DecidableEq, Repr

namespace TransferEncoding

instance : Inhabited TransferEncoding := ⟨⟨#["chunked"], by native_decide⟩⟩

/--
Creates a TransferEncoding with a single encoding.
-/
def new (encoding : String) (h : IsValidTransferEncoding #[encoding]) : TransferEncoding :=
  let encodings := #[encoding]
  ⟨encodings, h⟩

/--
Creates a TransferEncoding with multiple encodings.
-/
def ofArray (encodings : Array String) (h : IsValidTransferEncoding encodings) : TransferEncoding :=
  ⟨encodings, h⟩

/--
Parses a Transfer-Encoding header value (comma-separated list).
Returns `none` if the header is malformed according to HTTP/1.1 spec.
-/
def ofString? (s : String) : Option TransferEncoding :=
  let encodings := s.split (· == ',')
    |>.map (·.trimAscii.toString.toLower)
    |>.filter (!·.isEmpty)
    |>.toArray

  if encodings.isEmpty then
    none
  else
    if h : IsValidTransferEncoding encodings then
      some (ofArray encodings h)
    else
      none

/--
Creates a TransferEncoding from a string, panicking if invalid.
-/
def ofString! (s : String) : TransferEncoding :=
  match ofString? s with
  | some te => te
  | none => panic! s!"invalid transfer-encoding: {s.quote}"

/--
Checks if a specific encoding is present.
-/
def hasEncoding (te : TransferEncoding) (encoding : String) : Bool :=
  te.encodings.any (· == encoding.toLower)

/--
Checks if chunked encoding is present and valid.
Returns `some true` if chunked is present and valid (as the last encoding).
Returns `some false` if chunked is not present.
Returns `none` if the encoding list is invalid (should result in 400 Bad Request).
-/
def isChunked (te : TransferEncoding) : Option Bool :=
  if te.encodings.isEmpty then
    some false
  else
    some (te.encodings.back? == some "chunked")

/--
Gets the result of `isChunked`, panicking if the encoding is invalid.
-/
def isChunked! (te : TransferEncoding) : Bool :=
  match te.isChunked with
  | some b => b
  | none => panic! "invalid transfer-encoding: chunked encoding violations"

instance : ToString TransferEncoding where
  toString te := String.intercalate ", " te.encodings.toList

end TransferEncoding

instance : Header TransferEncoding where
  name _ := .new "transfer-encoding"
  value te := .ofString! <| String.intercalate ", " te.encodings.toList
  parse _ v := TransferEncoding.ofString? v.value

/--
Represents the Content-Type header, which indicates the media type of the resource.
-/
structure ContentType where
  /--
  The media type (e.g., "text/html", "application/json")
  -/
  mediaType : String

  /--
  Optional charset parameter
  -/
  charset : Option String := none
deriving BEq, DecidableEq, Repr

namespace ContentType

instance : Inhabited ContentType := ⟨⟨"text/plain", none⟩⟩

/--
Creates a ContentType with just a media type.
-/
def new (mediaType : String) : ContentType := ⟨mediaType, none⟩

/--
Creates a ContentType with a media type and charset.
-/
def withCharset (mediaType : String) (charset : String) : ContentType :=
  ⟨mediaType, some charset⟩

/--
Common content type for plain text documents.
-/
def textPlain : ContentType := new "text/plain"

/--
Common content type for HTML documents.
-/
def textHtml : ContentType := new "text/html"

/--
Common content type for JSON data.
-/
def applicationJson : ContentType := new "application/json"

/--
Common content type for XML documents.
-/
def applicationXml : ContentType := new "application/xml"

/--
Common content type for arbitrary binary data.
-/
def applicationOctetStream : ContentType := new "application/octet-stream"

instance : ToString ContentType where
  toString ct :=
    match ct.charset with
    | none => ct.mediaType
    | some cs => s!"{ct.mediaType}; charset={cs}"

end ContentType

instance : Header ContentType where
  name _ := .new "content-type"
  value ct := .ofString! (toString ct)
  parse _ v := some ⟨v.value, none⟩ -- Simplified parsing

/--
Represents the Host header, which specifies the domain name and optional port.
-/
structure Host where
  /--
  The hostname
  -/
  hostname : URI.Host

  /--
  Optional port number
  -/
  port : Option UInt16 := none

namespace Host

instance : Inhabited Host := ⟨⟨default, none⟩⟩

/--
Creates a Host header with just a hostname.
-/
def ofString? (hostname : String) : Option Host :=
  URI.Parser.parseHostHeader.run hostname.toUTF8
  |>.toOption
  |>.map (Function.uncurry Host.mk)

end Host

instance : Header Host where
  name _ := .new "host"
  value h := .ofString! <|
    (toString h.hostname) ++ (h.port.map ((":" ++ ·) ∘ toString) |>.getD "")

  parse _ := Host.ofString? ∘ Header.Value.value -- Simplified parsing

/--
Represents the Connection header, which controls whether the network connection
stays open after the current transaction finishes.
-/
inductive Connection where

  /--
  Keep the connection open for subsequent requests (HTTP/1.1 persistent connections).
  -/
  | keepAlive

  /--
  Close the connection after the current request-response cycle.
  -/
  | close

  /--
  A non-standard or extension connection option.
  -/
  | other (value : String)
deriving BEq, DecidableEq, Repr

namespace Connection

instance : Inhabited Connection := ⟨keepAlive⟩

/--
Attempts to parse a Connection header from a string.
-/
def ofString? (s : String) : Option Connection :=
  match s.trimAscii.toString.toLower with
  | "keep-alive" => some keepAlive
  | "close" => some close
  | x => some (other x)

/--
Creates a Connection header from a string, panicking if invalid.
-/
def ofString! (s : String) : Connection :=
  match ofString? s with
  | some c => c
  | none => panic! s!"invalid connection: {s.quote}"

instance : ToString Connection where
  toString
  | keepAlive => "keep-alive"
  | close => "close"
  | other v => v

end Connection

instance : Header Connection where
  name _ := .new "connection"
  value c := .ofString! (toString c)
  parse _ v := Connection.ofString? v.value

/--
Helper function to create a header name-value pair from any Header type.
-/
def toNameValue [h : Header α] (x : α) : Header.Name × Header.Value :=
  (h.name x, h.value x)

end Header
end Std.Http
