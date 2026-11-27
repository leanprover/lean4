/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
import Init.Data.Array
public import Std.Internal.Parsec
public import Std.Http.Data
public import Std.Http.Protocol.H1.Config
public import Std.Http.Protocol.H1.Message
public import Std.Http.Protocol.H1.Error
public import Std.Http.Protocol.H1.Host

public section

/-!
# HTTP/1.1 message rules

The rules of RFC 9110 and RFC 9112 that depend on a message head alone, not on the state of a
connection: which request targets a method allows, how the `Host` field is checked, which statuses
and methods leave a response without content, when a response starts a tunnel, how the body of a
received message is delimited, and which status answers each kind of failure. `H1.Machine` applies
them.
-/

namespace Std.Http.Protocol.H1.Rules

set_option linter.all true

open Std Std.Internal Http.Internal

/--
How the body of a message whose head was read is delimited (RFC 9112 §6.3).
-/
inductive BodyMode where
  /-- The body has exactly `n` bytes. -/
  | fixed (n : Nat)
  /-- The body uses the chunked transfer coding. -/
  | chunked
  /-- The body runs until the peer closes the connection. -/
  | eof

/--
Returns `true` when RFC semantics forbid a response payload body on the wire.
This includes informational responses, `204`, and `304`.

Reference: https://www.rfc-editor.org/rfc/rfc9112.html#name-message-body-length
-/
@[inline]
def responseMustNotHaveBody (status : Status) : Bool :=
  let code := status.toCode.toNat
  (100 ≤ code ∧ code < 200) ∨ code = 204 ∨ code = 304

/--
Returns `true` when a server must not send content in a response with `status`: the statuses of
`responseMustNotHaveBody`, and `205`. A 205 response still has a message body, of length zero, so
it is written with `Content-Length: 0` (RFC 9110 §15.3.6).
-/
@[inline]
def responseOmitsContent (status : Status) : Bool :=
  responseMustNotHaveBody status ∨ status == .resetContent

/--
Checks that request-target form and method are compatible
(`CONNECT` requires authority-form and `*` is reserved for `OPTIONS`).

Reference: https://www.rfc-editor.org/rfc/rfc9110#name-methods
-/
@[inline]
def isValidRequestTargetForMethod (message : Message.Head .receiving) : Bool :=
  match message.method, message.uri with

  -- Reference: https://www.rfc-editor.org/rfc/rfc9110#section-9.3.6
  | .connect, .authorityForm _ => true
  | .connect, _ => false
  | _, .authorityForm _ => false

  -- Reference: https://www.rfc-editor.org/rfc/rfc9110#name-options
  | .options, .asteriskForm => true
  | _, .asteriskForm => false

  | _, _ => true

/--
Returns `true` for the ports a `Host` field may leave out when it names the authority of a `CONNECT`
request: the defaults of `http` and `https`.
-/
@[inline]
def isDefaultTunnelPort (port : UInt16) : Bool :=
  port == 80 || port == 443

/--
Returns `true` when the `Host` field names the authority of a `CONNECT` request, allowing it to omit
a default port (see `isDefaultTunnelPort`).
-/
@[inline]
def hostAuthorityMatchesConnectAuthority
    (authority : URI.Authority)
    (hostHeader : Header.Host) : Bool :=
  authority.host == hostHeader.host &&
    (authority.port == hostHeader.port ||
      match authority.port, hostHeader.port with
      | .value port, .omitted => isDefaultTunnelPort port
      | _, _ => false)

/--
Validates the required `Host` header for HTTP/1.1 requests:
exactly one value that is either empty or parseable as a valid host.

As defined in RFC 9112 Section 3.2:

"A client MUST send a Host header field (Section 7.2 of [HTTP]) in all HTTP/1.1 request messages.
If the target URI includes an authority component, then a client MUST send a field value for Host that
is identical to that authority component, excluding any userinfo subcomponent and its "@"
delimiter (Section 4.2 of [HTTP]). If the authority component is missing or undefined for the target
URI, then a client MUST send a Host header field with an empty field value."

Reference: https://www.rfc-editor.org/rfc/rfc9112.html#name-request-target
-/
@[inline]
def hasSingleAcceptedHostHeader (message : Message.Head .receiving) : Bool :=
  match message.headers.getAll? Header.Name.host with
  | some #[hostValue] =>
    match message.uri with
    | .asteriskForm =>
      hostValue.value.isEmpty ∨ Host.isValid hostValue
    | .authorityForm authority =>
      match Header.Host.parse hostValue with
      -- RFC 9110 CONNECT examples allow `Host` to omit the default port
      -- while authority-form keeps the explicit tunnel port in request-target.
      | some hostHeader => hostAuthorityMatchesConnectAuthority authority hostHeader
      | none => false
    | _ =>
      -- origin-form, absolute-form, etc.: Host must be empty or well-formed.
      -- RFC 9112 §3.2.2: for absolute-form, the authority is in the URI; the Host
      -- header is left untouched so handlers can inspect what the client sent.
      hostValue.value.isEmpty ∨ Host.isValid hostValue
  | _ => false

/--
Validates an incoming request head and selects the body framing mode.
-/
def checkReceivingMessageHead (config : Config) (message : Message.Head .receiving) :
    Except H1.Error BodyMode := do
  -- URI Validation
  if !isValidRequestTargetForMethod message then
    throw .badMessage

  -- Host validation:
  -- • HTTP/1.1: a Host header is REQUIRED (RFC 9112 §3.2).
  -- • HTTP/1.0: Host is optional (RFC 2616 §14.23), but if present it must
  --   be a single, well-formed value (no duplicates, correct authority form).
  if message.version == .v11 || message.headers.contains .host then
    if !hasSingleAcceptedHostHeader message then
      throw .badMessage

  -- RFC 9110 §4.2.4: a recipient SHOULD treat userinfo in an http(s) URI as an error.
  if let .absoluteForm uri := message.uri then
    if (uri.scheme.val == "http" || uri.scheme.val == "https") && uri.authority.any (·.userInfo.isSome) then
      throw .badMessage

  -- Gets the size of the message.
  match message.getSize (allowEOFBody := true) with
  | some (.fixed n) => return .fixed n
  | some .chunked =>
    -- RFC 9112 §6.1: a server answers a transfer coding it does not understand with 501. The
    -- machine decodes the final `chunked` (`getSize` checked the codings end in it), and the
    -- application the codings in `acceptedTransferCodings`.
    match message.headers.getAll? Header.Name.transferEncoding >>=
        Header.TransferEncoding.parseFieldLines? with
    | some codings =>
      if codings.pop.all (fun c => config.acceptedTransferCodings.any (·.toLower == c)) then
        return .chunked
      else
        throw .unsupportedTransferCoding
    | none => throw .badMessage
  | none => throw .badMessage

/--
Returns `true` when a response with `status` to a request with `method` turns the connection into a
tunnel: a 2xx to `CONNECT`. Such a response has no content and no framing fields (RFC 9110 §9.3.6),
and the connection carries no more HTTP after its head: a server, which does not tunnel, closes it,
and a client leaves the tunnel's bytes unread.
-/
@[inline]
def startsTunnel (method : Method) (status : Status) : Bool :=
  method == .connect ∧ status.isSuccess

/--
Returns `true` when user-provided headers include body framing fields.
-/
@[inline]
def hasFramingHeaders (message : Message.Head dir) : Bool :=
  message.headers.map.entries.any fun (name, _) =>
    name == Header.Name.contentLength || name == Header.Name.transferEncoding

/--
Returns `true` when a response's transfer codings end in a coding other than `chunked` and no
`Content-Length` competes with them. RFC 9112 §6.3 rule 4: such a body has no length of its own and
runs until the server closes the connection.
-/
def hasCloseDelimitedCoding (message : Message.Head .sending) : Bool :=
  message.version == .v11 && !message.headers.contains Header.Name.contentLength &&
    match message.headers.getAll? Header.Name.transferEncoding with
    | some values => Header.TransferEncoding.finalCodingIsChunked? values == some false
    | none => false

/--
Validates an incoming response head, answering a request with `requestMethod`, and selects its body
framing mode.

RFC 9112 §6.3 rules 1 and 2: a response to `HEAD`, every 1xx, 204 and 304 response, and a 2xx
response to `CONNECT` end at the header block whatever their framing fields say, so those fields are
not validated. What follows a 2xx to `CONNECT` is the tunnel, which `processHeaders` leaves unread.
-/
def checkSendingMessageHead (requestMethod : Method) (message : Message.Head .sending) :
    Except H1.Error BodyMode :=
  if requestMethod == .head || responseMustNotHaveBody message.status ||
      startsTunnel requestMethod message.status then
    pure (.fixed 0)
  else
    match message.getSize false with
    | some (.fixed n) => pure (.fixed n)
    | some .chunked => pure .chunked
    | none =>
      if !hasFramingHeaders message || hasCloseDelimitedCoding message then pure .eof
      else throw .badMessage

/--
Returns `true` when response status forbids framing headers entirely
(informational and `204` responses).
-/
@[inline]
def responseForbidsFramingHeaders (status : Status) : Bool :=
  let code := status.toCode.toNat
  (100 ≤ code ∧ code < 200) ∨ code = 204

/--
The failure `rejectOutgoing` reports for a head that contradicts its body: a mistake of the sender's own code, not a malformed
message from the peer. A server passes it to `Handler.onFailure`.
-/
def framingMismatchError : H1.Error :=
  .other "Content-Length or Transfer-Encoding contradicts the body"

/-- Maps a reader failure to an HTTP status code. -/
def errorResponseStatus (error : H1.Error) : Status :=
  match error with
  | .unsupportedVersion => .httpVersionNotSupported
  | .unsupportedTransferCoding => .notImplemented
  | .unsupportedMethod => .notImplemented
  | .entityTooLarge => .payloadTooLarge
  | .uriTooLong => .uriTooLong
  | .tooManyHeaders => .requestHeaderFieldsTooLarge
  | .headersTooLarge => .requestHeaderFieldsTooLarge
  | _ => .badRequest

/--
Classifies hard request start-line parse failures into protocol-level errors.
-/
@[inline]
def classifyStartLineHardError : Std.Internal.Parsec.Error → H1.Error
  | .other "uri too long" => .uriTooLong
  | .other "unrecognized method" => .unsupportedMethod
  | _ => .badMessage

/--
Classifies hard field-line parse failures: a name or value over its limit is too large, as too many
fields are (RFC 6585 §5 answers both with 431), and anything else is malformed.
-/
@[inline]
def classifyFieldLineHardError : Std.Internal.Parsec.Error → H1.Error
  | .other "header name too long" | .other "header value too long" => .headersTooLarge
  | _ => .badMessage

end Std.Http.Protocol.H1.Rules
