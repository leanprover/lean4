/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Data.URI
public import Std.Http.Data.Headers.Name
public import Std.Http.Data.Headers.Value
public import Std.Internal.Parsec.Basic
import Init.Data.String.Search

public section

/-!
# Header Typeclass and Common Headers

This module defines the `Header` typeclass for typed HTTP headers and some common header parsers.

Reference: https://www.rfc-editor.org/rfc/rfc9110.html#name-representation-data-and-met
-/

namespace Std.Http

set_option linter.all true

open Internal

/--
Typeclass for typed HTTP headers that can be parsed from and serialized to header values.
-/
class Header (α : Type) where

  /--
  Parses a header value into the typed representation.
  -/
  parse : Header.Value → Option α

  /--
  Serializes the typed representation back to a name-value pair.
  -/
  serialize : α → Header.Name × Header.Value

instance [h : Header α] : Encode .v11 α where
  encode buffer a :=
    let (name, value) := h.serialize a
    buffer.writeString s!"{name}: {value}\r\n"

namespace Header

private def parseTokenList (v : Value) : Option (Array String) := do
  let rawParts := v.value.split (· == ',')
  let parts := rawParts.map (·.trimAscii)

  guard (parts.all (¬·.isEmpty))

  return parts.toArray.map (fun s => s.toString.toLower)

/--
The `Content-Length` header, representing the size of the message body in bytes.
Parses only valid natural number values.

Reference: https://www.rfc-editor.org/rfc/rfc9110.html#section-8.6-2
-/
structure ContentLength where

  /--
  The content length in bytes.
  -/
  length : Nat
deriving BEq, Repr

namespace ContentLength

/--
Parses a content length header value.
-/
def parse (v : Value) : Option ContentLength :=
  let s := v.value
  if s.isEmpty || !s.all Char.isDigit then none
  else s.toNat?.map (.mk)

/--
Serializes a content length header back to a name-value pair.
-/
def serialize (h : ContentLength) : Name × Value :=
  (Header.Name.contentLength, Value.ofString! (toString h.length))

instance : Header ContentLength := ⟨parse, serialize⟩

end ContentLength

/--
Validates the chunked placement rules for the Transfer Encoding header. Returns `false` if the
encoding list violates the constraints.

Reference: https://www.rfc-editor.org/rfc/rfc9112#section-6.1
-/
@[expose]
def TransferEncoding.Validate (codings : Array String) : Bool :=
  if codings.isEmpty || codings.any (fun coding => !isToken coding) then
    false
  else
    let chunkedCount := codings.filter (· == "chunked") |>.size

    -- the sender MUST either apply chunked as the final transfer coding
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

Reference: https://www.rfc-editor.org/rfc/rfc9112#section-6.1
-/
structure TransferEncoding where

  /--
  The ordered list of transfer codings.
  -/
  codings : Array String

  /--
  Proof that the transfer codings satisfy the chunked placement rules.
  -/
  isValid : TransferEncoding.Validate codings = true

deriving Repr

namespace TransferEncoding

/--
Returns `true` if the transfer encoding ends with chunked.
-/
def isChunked (te : TransferEncoding) : Bool :=
  te.codings.back? == some "chunked"

/--
Parses a comma-separated list of transfer codings from a header value, validating chunked placement.
-/
def parse (v : Value) : Option TransferEncoding := do
  let codings ← parseTokenList v
  if h : TransferEncoding.Validate codings then
    some ⟨codings, h⟩
  else
    none

/--
Serializes a transfer encoding back to a comma-separated header value.
-/
def serialize (te : TransferEncoding) : Header.Name × Header.Value :=
  let value := ",".intercalate (te.codings.toList)
  (Header.Name.transferEncoding, Value.ofString! value)

instance : Header TransferEncoding := ⟨parse, serialize⟩

end TransferEncoding

/--
The `Connection` header, represented as a list of connection option tokens.

Reference: https://www.rfc-editor.org/rfc/rfc9110.html#name-connection
-/
structure Connection where
  /--
  The normalized connection-option tokens.
  -/
  tokens : Array String

  /--
  Proof that all tokens satisfy `isToken`.
  -/
  valid : tokens.all isToken = true
deriving Repr

namespace Connection

/--
Checks whether a specific token is present in the `Connection` header value.
-/
def containsToken (connection : Connection) (token : String) : Bool :=
  let token := token.trimAscii.toString.toLower
  connection.tokens.any (· == token)

/--
Checks whether the `Connection` header requests connection close semantics.
-/
def shouldClose (connection : Connection) : Bool :=
  connection.containsToken "close"

/--
Parses a `Connection` header value into normalized tokens.
-/
def parse (v : Value) : Option Connection := do
  let tokens ← parseTokenList v
  if h : tokens.all isToken = true then
    some ⟨tokens, h⟩
  else
    none

/--
Serializes a `Connection` header back to a comma-separated value.
-/
def serialize (connection : Connection) : Header.Name × Header.Value :=
  let value := ",".intercalate connection.tokens.toList
  (Header.Name.connection, Value.ofString! value)

instance : Header Connection := ⟨parse, serialize⟩

end Connection

/--
The `Host` header.

Represents the authority component of a URI:
  host [ ":" port ]

Reference: https://www.rfc-editor.org/rfc/rfc9110.html#name-host-and-authority
-/
structure Host where
  /--
  Host name (reg-name, IPv4, or IPv6 literal).
  -/
  host : URI.Host

  /--
  Optional port.
  -/
  port : URI.Port
deriving Repr, BEq

namespace Host

/--
Parses a `Host` header value.
-/
def parse (v : Value) : Option Host :=
  let parsed := (Std.Http.URI.Parser.parseHostHeader <* Std.Internal.Parsec.eof).run v.value.toUTF8
  match parsed with
  | .ok ⟨host, port⟩ => some ⟨host, port⟩
  | .error _ => none

/--
Serializes a `Host` header back to a name and a value.
-/
def serialize (host : Host) : Header.Name × Header.Value :=
  let value := match host.port with
    | .value port => Header.Value.ofString! s!"{host.host}:{port}"
    | .empty => Header.Value.ofString! s!"{host.host}:"
    | .omitted => Header.Value.ofString! <| toString host.host

  (.mk "host", value)

instance : Header Host := ⟨parse, serialize⟩

end Host

/--
The `Expect` header.

Represents an expectation token.
The only standardized expectation is `100-continue`.

Reference: https://www.rfc-editor.org/rfc/rfc9110.html#name-expect
-/
structure Expect where
deriving Repr, BEq

namespace Expect

/--
Parses an `Expect` header.

Succeeds only if the value is exactly `100-continue`
(case-insensitive, trimmed).
-/
def parse (v : Value) : Option Expect :=
  let normalized := v.value.trimAscii.toString.toLower

  if normalized == "100-continue" then
    some ⟨⟩
  else
    none

/--
Serializes an `Expect` header.
-/
def serialize (_ : Expect) : Header.Name × Header.Value :=
  (Header.Name.expect, Value.ofString! "100-continue")

instance : Header Expect := ⟨parse, serialize⟩

end Expect

end Std.Http.Header
