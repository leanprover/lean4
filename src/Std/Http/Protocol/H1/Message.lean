/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
import Init.Data.Array
public import Std.Http.Protocol.H1.Basic

public section

/-!
# HTTP/1.1 message rules

What a response's status allows it to carry, what a message's framing fields say about its body, and
whether a message keeps the connection open.
-/

namespace Std.Http.Protocol.H1

set_option linter.all true

/--
What a response with a given status may carry (RFC 9110 §15).
-/
inductive ContentRule where
  /--
  1xx and 204: no content, and no `Content-Length` or `Transfer-Encoding` field.
  -/
  | none

  /--
  304: no content. Framing fields would describe the representation it stands for.
  -/
  | notModified

  /--
  205: no content, written as `Content-Length: 0` (RFC 9110 §15.3.6).
  -/
  | empty

  /--
  Every other status.
  -/
  | any
deriving BEq

/--
What a response with this status may carry.
-/
def _root_.Std.Http.Status.contentRule (status : Status) : ContentRule :=
  let code := status.toCode
  if (100 ≤ code ∧ code < 200) ∨ code = 204 then .none
  else if code = 304 then .notModified
  else if code = 205 then .empty
  else .any

/--
Whether a response turns its connection into a tunnel: a 2xx answer to `CONNECT` (RFC 9110 §9.3.6).
It has no content and no framing fields, and no HTTP follows its head.
-/
@[inline]
def startsTunnel (requestMethod : Method) (status : Status) : Bool :=
  requestMethod == .connect && status.isSuccess

/--
Whether a response ends HTTP on its connection: after `101 Switching Protocols` the connection
speaks the protocol it switched to (RFC 9110 §15.2.2), and after a tunnel's head (`startsTunnel`) it
carries the tunnel's bytes.
-/
@[inline]
def leavesHttp (requestMethod : Method) (status : Status) : Bool :=
  status.toCode == 101 || startsTunnel requestMethod status

/--
What a message's `Content-Length` and `Transfer-Encoding` fields say about its body.
-/
inductive FramingFields where
  /--
  Neither field.
  -/
  | none

  /--
  One valid `Content-Length` and no `Transfer-Encoding`.
  -/
  | length (n : Nat)

  /--
  Transfer codings ending in the only `chunked`, and no `Content-Length`.
  -/
  | chunked (codings : Array String)

  /--
  Transfer codings that do not end in `chunked`, and no `Content-Length`.
  -/
  | unchunked

  /--
  Anything else: several or malformed `Content-Length` fields, both fields, or malformed codings.
  Each could be read differently by another recipient, so such a message is rejected.
  -/
  | invalid

/--
Classifies a message's framing fields.
-/
def Message.Head.framingFields (message : Message.Head dir) : FramingFields :=
  let contentLength := message.headers.getAll? .contentLength
  match message.headers.getAll? .transferEncoding with
  | none =>
    match contentLength with
    | none => .none
    | some #[value] =>
      match Header.ContentLength.parse value with
      | some cl => .length cl.length
      | none => .invalid
    | some _ => .invalid
  | some values =>
    if contentLength.isSome then .invalid
    else
      match Header.TransferEncoding.parseFieldLines? values with
      | none => .invalid
      | some codings =>
        if codings.back? != some "chunked" then .unchunked
        else if codings.count "chunked" == 1 then .chunked codings
        else .invalid

/--
Whether a message has a `Content-Length` or `Transfer-Encoding` field.
-/
@[inline]
def Message.Head.hasFramingFields (message : Message.Head dir) : Bool :=
  message.headers.map.entries.any fun (name, _) =>
    name == Header.Name.contentLength || name == Header.Name.transferEncoding

/--
The body length a message's framing fields state. With `allowEOFBody`, a message with neither field
has an empty body. HTTP/1.0 has no chunked coding.
-/
def Message.Head.getSize (message : Message.Head dir) (allowEOFBody : Bool) : Option Body.Length :=
  match message.framingFields with
  | .none => if allowEOFBody then some (.fixed 0) else Option.none
  | .length n => some (.fixed n)
  | .chunked _ => if message.version == .v10 then Option.none else some .chunked
  | .unchunked | .invalid => Option.none

/--
The tokens of the `Connection` field lines `values`, and whether every line parsed.
-/
def connectionOptions (values : Array Header.Value) : Array String × Bool :=
  values.foldl (init := (#[], true)) fun (tokens, ok) value =>
    match Header.Connection.parse value with
    | some connection => (tokens ++ connection.tokens, ok)
    | none => (tokens, false)

/--
Whether a message lets the connection stay open after it (RFC 9112 §9.3): not if `Connection` has
`close`, whatever the version; otherwise HTTP/1.1 does, and HTTP/1.0 only with `keep-alive`. A
`Connection` field that does not parse closes it.
-/
def Message.Head.shouldKeepAlive (message : Message.Head dir) : Bool :=
  match message.headers.getAll? .connection with
  | none => message.version == .v11
  | some values =>
    let (tokens, ok) := connectionOptions values
    ok && !tokens.contains "close" && (message.version == .v11 || tokens.contains "keep-alive")

end Std.Http.Protocol.H1
