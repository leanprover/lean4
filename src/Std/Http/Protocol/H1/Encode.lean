/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
import Init.Data.Array
public import Std.Http.Data
public import Std.Http.Internal
public import Std.Http.Protocol.H1.Message
public import Std.Http.Protocol.H1.Rules

public section

/-!
# HTTP/1.1 head encoding

The bytes of the message heads `H1.Machine` writes: a server's response heads, including the error
responses it writes itself, and a client's request heads, each with the `Connection` and framing
fields the machine chose in place of the caller's.
-/

namespace Std.Http.Protocol.H1.Encode

set_option linter.all true

open Std Std.Internal Http.Internal Rules

/--
The `Transfer-Encoding` value for a chunked message: the caller's own codings when they end in
`chunked` (`gzip, chunked`), since the body bytes were coded for them, and `chunked` otherwise.
Several field lines are written as one.
-/
def chunkedCodings (headers : Headers) : Header.Value :=
  match headers.getAll? Header.Name.transferEncoding with
  | some values =>
    if Header.TransferEncoding.finalCodingIsChunked? values == some true then
      match values with
      | #[value] => value
      | _ =>
        let combined := ", ".intercalate (values.map (·.value)).toList
        (Header.Value.ofString? combined).getD (.mk "chunked")
    else
      .mk "chunked"
  | none => .mk "chunked"

/--
The tokens of the `Connection` field the machine writes: the sender's own connection options, then
`close` when the connection ends, or `keep-alive` when an HTTP/1.0 connection persists (RFC 2616
§19.7.1). The sender's `close` and `keep-alive` are dropped, since the machine decides those itself;
its other options are kept, such as the `upgrade` that RFC 9110 §7.8 requires next to `Upgrade`.
-/
def connectionTokens (headers : Headers) (keepAlive : Bool) (version : Version) :
    Array String :=
  let options : Array String :=
    match headers.getAll? Header.Name.connection with
    | none => #[]
    | some values =>
      values.foldl (init := #[]) fun acc value =>
        match Header.Connection.parse value with
        | some connection =>
          acc ++ connection.tokens.filter (fun t => t != "close" && t != "keep-alive")
        | none => acc
  if !keepAlive then options.push "close"
  else if version == .v10 then options.push "keep-alive"
  else options

/--
The status line of a `200 OK` response.
-/
def okStatusLine : ByteArray :=
  "HTTP/1.1 200 OK\r\n".toUTF8

/--
The start of a `Content-Length` field line.
-/
def contentLengthPrefix : ByteArray :=
  "Content-Length: ".toUTF8

/--
Encodes a server response head. The handler's fields are written in order without `Connection`,
`Content-Length` and `Transfer-Encoding`, then `Date` and `Server` unless the handler set them, then
the `Connection` and framing fields the machine chose. The handler's own connection options (such as
`upgrade`) go in that `Connection` field, before the machine's `close` or `keep-alive`.

`version` is the request's version and selects the framing. The status line always carries
HTTP/1.1, the highest version the server conforms to (RFC 9110 §6.2). A `tunnel` response (see
`startsTunnel`) has no framing fields.
-/
def encodeServerHead (head : Response.Head) (version : Version) (keepAlive : Bool)
    (date : Option Header.Value) (agentName : Option Header.Value) (size : Body.Length)
    (tunnel : Bool := false) : ByteArray :=
  let status := head.status
  -- Room for a typical head, so the appends below rarely grow it.
  let out := ByteArray.emptyWithCapacity 256
  let out : ByteArray :=
    match status with
    | .ok => out ++ okStatusLine
    | status => (out ++ Version.v11 ++ ' ' ++ status).push '\r'.toUInt8 |>.push '\n'.toUInt8
  let out : ByteArray := head.headers.fold out fun out name value =>
    if name == Header.Name.connection || name == Header.Name.contentLength ||
        name == Header.Name.transferEncoding then
      out
    else
      appendFieldLine out name value
  let out : ByteArray :=
    match date with
    | some date =>
      if head.headers.contains Header.Name.date then out
      else appendFieldLine out Header.Name.date date
    | none => out
  let out : ByteArray :=
    match agentName with
    | some server =>
      if head.headers.contains Header.Name.server then out
      else appendFieldLine out Header.Name.server server
    | none => out
  let tokens := connectionTokens head.headers keepAlive version
  let out : ByteArray :=
    if tokens.isEmpty then out
    else out ++ "Connection: " ++ ", ".intercalate tokens.toList ++ "\r\n"
  -- Framing fields are omitted for bodyless status codes (RFC 9110 §8.6, §15.4.5) and for
  -- HTTP/1.0 connection-close framing (RFC 7230 §3.3.1).
  let out : ByteArray :=
    if responseForbidsFramingHeaders status ∨ status == .notModified ∨ tunnel then
      out
    else
      match size with
      | .fixed n => (out ++ contentLengthPrefix ++ n).push '\r'.toUInt8 |>.push '\n'.toUInt8
      | .chunked =>
        if version == .v10 then out
        else appendFieldLine out Header.Name.transferEncoding (chunkedCodings head.headers)
  out.push '\r'.toUInt8 |>.push '\n'.toUInt8

/--
The content of an error response the machine writes itself: the reason phrase, and for 505 the
versions the server supports (RFC 9110 §15.6.6).
-/
def errorContent (status : Status) : ByteArray :=
  match status with
  | .httpVersionNotSupported =>
    "HTTP Version Not Supported: this server supports HTTP/1.0 and HTTP/1.1\n".toUTF8
  | _ => (status.reasonPhrase ++ "\n").toUTF8

/--
The head of an error response the machine writes itself, which carries `errorContent` as
`text/plain`.
-/
def errorHead (status : Status) (headers : Headers := .empty) : Response.Head :=
  { status, headers := headers.insert Header.Name.contentType (.mk "text/plain; charset=utf-8") }

/--
Encodes a client request head: the caller's fields, then `User-Agent` unless the caller set it, with
the `Connection` field and the framing fields the machine chose in place of the caller's.
-/
def encodeClientHead (head : Request.Head) (keepAlive : Bool) (agentName : Option Header.Value)
    (size : Body.Length) : ByteArray :=
  let headers := head.headers
  -- RFC 9110 §8.6: no `Content-Length` on a request without content whose method anticipates
  -- none, unless the caller set a framing field.
  let framed :=
    !(size == .fixed 0 ∧ !head.method.anticipatesContent ∧
      !hasFramingHeaders (dir := .receiving) head)
  let out : ByteArray :=
    ByteArray.emptyWithCapacity 256 ++ head.method ++ ' ' ++ head.uri ++ ' ' ++ head.version
  let out : ByteArray := out.push '\r'.toUInt8 |>.push '\n'.toUInt8
  let out : ByteArray := headers.fold out fun out name value =>
    if name == Header.Name.connection ||
        (framed && (name == Header.Name.contentLength || name == Header.Name.transferEncoding)) then
      out
    else
      appendFieldLine out name value
  let out : ByteArray :=
    match agentName with
    | some userAgent =>
      if headers.contains Header.Name.userAgent then out
      else appendFieldLine out Header.Name.userAgent userAgent
    | none => out
  -- The request's own version: the reader may already hold the next response's status line.
  let tokens := connectionTokens headers keepAlive head.version
  let out : ByteArray :=
    if tokens.isEmpty then out
    else out ++ "Connection: " ++ ", ".intercalate tokens.toList ++ "\r\n"
  let out : ByteArray :=
    if !framed then out
    else
      match size with
      | .fixed n => (out ++ contentLengthPrefix ++ n).push '\r'.toUInt8 |>.push '\n'.toUInt8
      | .chunked => appendFieldLine out Header.Name.transferEncoding (chunkedCodings headers)
  out.push '\r'.toUInt8 |>.push '\n'.toUInt8

end Std.Http.Protocol.H1.Encode
