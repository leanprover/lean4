/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Http.Data.Headers.Name
public import Std.Internal.Http.Data.Headers.Value
public import Std.Internal.Http.Internal

public section

/-!
# Header Typeclass and Common Headers

This module defines the `Header` typeclass for typed HTTP headers and some common header parsers.
-/

namespace Std.Http

set_option linter.all true

open Internal

/--
Typeclass for typed HTTP headers that can be parsed from and serialized to header values.
-/
class Header (α : Type) where

  /--
  Parse a header value into the typed representation.
  -/
  parse : Header.Value → Option α

  /--
  Serialize the typed representation back to a name-value pair.
  -/
  serialize : α → Header.Name × Header.Value

/--
An `Encode` instance can be derived from any `Header` instance by serializing to the wire format
`Name: Value\r\n`.
-/
instance [h : Header α] : Encode .v11 α where
  encode buffer a :=
    let (name, value) := h.serialize a
    buffer.writeString s!"{name}: {value}\r\n"

namespace Header

/--
The `Content-Length` header, representing the size of the message body in bytes.
Parses only valid natural number values.
-/
structure ContentLength where

  /--
  The content length in bytes.
  -/
  length : Nat
deriving BEq, Repr

namespace ContentLength

/--
Parse a content length header from a name and value
.-/
def parse (v : Value) : Option ContentLength :=
   v.value.toNat?.map (.mk)

/--
Serialize a content length header back to a name-value pair
-/
def serialize (h : ContentLength) : Name × Value :=
  (Header.Name.contentLength, Value.ofString! (toString h.length))

instance : Header ContentLength := ⟨parse, serialize⟩

end ContentLength

/--
Validate the chunked placement rules. Returns `none` if the encoding list violates the constraints.
-/
@[expose]
def TransferEncoding.Validate (codings : Array String) : Bool :=
  if codings.isEmpty || codings.any (· == "") then
    false
  else
    let chunkedCount := codings.filter (· == "chunked") |>.size
    let lastIsChunked := codings.back? == some "chunked"
    if chunkedCount > 1 then
      false
    else if chunkedCount == 1 && !lastIsChunked then
      false
    else
      true

/--
The `Transfer-Encoding` header, representing the list of transfer codings applied to the message body.

Validation rules (RFC 9112 Section 6.1):
- "chunked" may appear at most once.
- If "chunked" is present, it must be the last encoding in the list.
-/
structure TransferEncoding where

  /--
  The ordered list of transfer codings.
  -/
  codings : Array String

  /--
  Valid encodings.
  -/
  valid : TransferEncoding.Validate codings = true

deriving Repr

namespace TransferEncoding

/--
Returns `true` if the transfer encoding ends with chunked.
-/
def isChunked (te : TransferEncoding) : Bool :=
  te.codings.back? == some "chunked"

/--
Parse a comma-separated list of transfer codings from a header value, validating chunked placement.
-/
def parse (v : Value) : Option TransferEncoding :=
  let codings := v.value.split (· == ',') |>.toArray.map (·.trimAscii.toString.toLower)
  if h : TransferEncoding.Validate codings then
    some ⟨codings, h⟩
  else
    none

/--
Serialize a transfer encoding back to a comma-separated header value.
-/
def serialize (te : TransferEncoding) : Header.Name × Header.Value :=
  let value := ",".intercalate (te.codings.toList)
  (Header.Name.transferEncoding, Value.ofString! value)

instance : Header TransferEncoding := ⟨parse, serialize⟩

end Std.Http.Header.TransferEncoding
