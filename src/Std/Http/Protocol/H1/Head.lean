/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
import Init.Data.Array
public import Std.Http.Protocol.H1.Config
public import Std.Http.Protocol.H1.Message
public import Std.Http.Protocol.H1.Reader

public section

/-!
# HTTP/1.1 message heads

Checking the head of a received message and choosing how to read its body, and encoding the head of
a message to send.
-/

namespace Std.Http.Protocol.H1

set_option linter.all true

open Std.Http.Internal

/--
Whether a request-target's form suits the method: authority-form only for `CONNECT`, which requires
it (RFC 9110 §9.3.6), and `*` only for `OPTIONS` (RFC 9110 §9.3.7).
-/
@[inline]
private def isValidRequestTargetForMethod (message : Message.Head .receiving) : Bool :=
  match message.uri with
  | .authorityForm _ => message.method == .connect
  | .asteriskForm => message.method == .options
  | _ => message.method != .connect

/--
Whether a `Host` field matches a `CONNECT` request's authority. RFC 9110's `CONNECT` examples leave
the default port out of `Host` while the authority-form target keeps it.
-/
@[inline]
private def hostMatchesConnectAuthority (authority : URI.Authority) (host : Header.Host) : Bool :=
  authority.host == host.host &&
    (authority.port == host.port ||
      match authority.port, host.port with
      | .value port, .omitted => port == 80 || port == 443
      | _, _ => false)

/--
Whether a request has exactly one `Host` field that is empty or a valid host, matching the authority
of a `CONNECT` request (RFC 9112 §3.2). For an absolute-form target the field is kept as sent, so a
handler can inspect it (RFC 9112 §3.2.2).
-/
@[inline]
private def hasSingleAcceptedHostHeader (message : Message.Head .receiving) : Bool :=
  match message.headers.getAll? Header.Name.host with
  | some #[hostValue] =>
    let parsed := Header.Host.parse hostValue
    match message.uri with
    | .authorityForm authority =>
      match parsed with
      | some host => hostMatchesConnectAuthority authority host
      | none => false
    | _ => hostValue.value.isEmpty ∨ parsed.isSome
  | _ => false

/--
Whether an absolute-form `http` or `https` request-target carries userinfo, which a recipient should
treat as an error (RFC 9110 §4.2.4).
-/
@[inline]
private def hasHttpUserInfo (message : Message.Head .receiving) : Bool :=
  match message.uri with
  | .absoluteForm uri =>
    (uri.scheme.val == "http" || uri.scheme.val == "https") && uri.authority.any (·.userInfo.isSome)
  | _ => false

/--
Checks a received request head and chooses how to read its body. HTTP/1.1 requires `Host`; HTTP/1.0
allows leaving it out, but not a malformed or repeated one. A server answers a transfer coding it
does not decode with 501 (RFC 9112 §6.1): the machine decodes the final `chunked`, and the
application the codings in `Config.acceptedTransferCodings`.
-/
def checkRequestHead (config : Config) (message : Message.Head .receiving) :
    Except Error Reader.BodyState :=
  if !isValidRequestTargetForMethod message then
    .error .badMessage
  else if (message.version == .v11 || message.headers.contains .host) &&
      !hasSingleAcceptedHostHeader message then
    .error .badMessage
  else if hasHttpUserInfo message then
    .error .badMessage
  else
    match message.framingFields with
    | .none => .ok (.fixed 0)
    | .length n => .ok (.fixed n)
    | .chunked codings =>
      if message.version == .v10 then
        .error .badMessage
      else if codings.pop.all (fun c => config.acceptedTransferCodings.any (·.toLower == c)) then
        .ok .chunkedSize
      else
        .error .unsupportedTransferCoding
    | .unchunked | .invalid => .error .badMessage

/--
Checks a received response head, answering a request with `requestMethod`, and chooses how to read
its body. A response to `HEAD`, and every 1xx, 204 and 304 response, ends at its header section
whatever its framing fields say (RFC 9112 §6.3 rule 1), and so does a 2xx answer to `CONNECT` (rule
2). Without framing fields, or with codings that
do not end in `chunked`, the body runs until the server closes the connection (rule 4 and rule 8).
-/
def checkResponseHead (requestMethod : Method) (message : Message.Head .sending) :
    Except Error Reader.BodyState :=
  if requestMethod == .head || message.status.contentRule matches .none | .notModified ||
      leavesHttp requestMethod message.status then
    .ok (.fixed 0)
  else
    match message.framingFields with
    | .none => .ok .closeDelimited
    | .length n => .ok (.fixed n)
    | .chunked _ => if message.version == .v10 then .error .badMessage else .ok .chunkedSize
    | .unchunked => if message.version == .v11 then .ok .closeDelimited else .error .badMessage
    | .invalid => .error .badMessage

/--
Whether a request asks for `100 Continue` before its body. A server must not send a 1xx response to
an HTTP/1.0 client (RFC 9110 §15.2).
-/
@[inline]
def expectsContinue (message : Message.Head .receiving) : Bool :=
  message.version == .v11 &&
    match message.headers.getAll? Header.Name.expect with
    | some #[value] => (Header.Expect.parse value).isSome
    | _ => false

/--
The `Transfer-Encoding` value of a chunked message: the sender's own codings when they end in
`chunked` (`gzip, chunked`), since the body was coded for them, and `chunked` otherwise. Several
field lines are written as one.
-/
private def chunkedCodings (headers : Headers) : Header.Value :=
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
Appends the `Connection` field the machine writes: the sender's own connection options without
`close` and `keep-alive`, which the machine decides, then `close` when the connection ends, or
`keep-alive` when an HTTP/1.0 connection persists (RFC 2616 §19.7.1). Options such as the `upgrade`
that RFC 9110 §7.8 requires next to `Upgrade` are kept.
-/
private def appendConnection (out : ByteArray) (headers : Headers) (keepAlive : Bool)
    (version : Version) : ByteArray :=
  let options :=
    match headers.getAll? Header.Name.connection with
    | none => #[]
    | some values => (connectionOptions values).1.filter (fun t => t != "close" && t != "keep-alive")
  let options :=
    if !keepAlive then options.push "close"
    else if version == .v10 then options.push "keep-alive"
    else options
  if options.isEmpty then out else out ++ "Connection: " ++ ", ".intercalate options.toList ++ "\r\n"

/--
Appends the sender's header fields, without the `Connection`, `Content-Length` and
`Transfer-Encoding` fields that the machine writes itself.
-/
@[inline]
private def appendSenderFields (out : ByteArray) (headers : Headers) : ByteArray :=
  headers.fold out fun out name value =>
    if name == Header.Name.connection || name == Header.Name.contentLength ||
        name == Header.Name.transferEncoding then
      out
    else
      appendFieldLine out name value

/--
Appends `name: value` unless the sender set `name`.
-/
@[inline]
private def appendDefault (out : ByteArray) (headers : Headers) (name : Header.Name)
    (value : Option Header.Value) : ByteArray :=
  match value with
  | some value => if headers.contains name then out else appendFieldLine out name value
  | none => out

/--
Appends the framing field for a body of length `size`.
-/
@[inline]
private def appendFraming (out : ByteArray) (headers : Headers) (size : Body.Length) : ByteArray :=
  match size with
  | .fixed n => out ++ "Content-Length: " ++ n ++ "\r\n"
  | .chunked => appendFieldLine out Header.Name.transferEncoding (chunkedCodings headers)

/--
Encodes a response head, answering a request of HTTP version `version`, with a body of length
`size`. The sender's fields come first, then `Date` and `Server` unless it set them, then
`Connection` and the framing field, unless `rule` says the response has none. The status line always
says HTTP/1.1, the highest version the server conforms to (RFC 9110 §6.2). Statuses without content
get no framing field (RFC 9110 §8.6, §15.4.5), and neither does the connection-close body of an
HTTP/1.0 response.
-/
def encodeResponseHead (head : Response.Head) (version : Version) (keepAlive : Bool)
    (date agentName : Option Header.Value) (size : Body.Length)
    (rule : ContentRule := head.status.contentRule) : ByteArray :=
  let out := ByteArray.empty ++ Version.v11 ++ ' ' ++ head.status ++ "\r\n"
  let out := appendSenderFields out head.headers
  let out := appendDefault out head.headers Header.Name.date date
  let out := appendDefault out head.headers Header.Name.server agentName
  let out := appendConnection out head.headers keepAlive version
  let out :=
    if rule matches .none | .notModified then out
    else if size matches .chunked && version == .v10 then out
    else appendFraming out head.headers size
  out ++ "\r\n"

/--
Encodes a request head with a body of length `size`. The sender's fields come first, then
`User-Agent` unless it set one, then `Connection` and the framing field. A request without content
whose method anticipates none gets no `Content-Length`, unless the sender set a framing field (RFC
9110 §8.6).
-/
def encodeRequestHead (head : Request.Head) (keepAlive : Bool) (agentName : Option Header.Value)
    (size : Body.Length) : ByteArray :=
  let out := ByteArray.empty ++ head.method ++ ' ' ++ head.uri ++ ' ' ++ head.version ++ "\r\n"
  let out := appendSenderFields out head.headers
  let out := appendDefault out head.headers Header.Name.userAgent agentName
  let out := appendConnection out head.headers keepAlive head.version
  let out :=
    if size == .fixed 0 && !head.method.anticipatesContent &&
        !Message.Head.hasFramingFields (dir := .receiving) head then
      out
    else
      appendFraming out head.headers size
  out ++ "\r\n"

/--
The status a server answers a failure to read a request with.
-/
def Error.responseStatus : Error → Status
  | .unsupportedVersion => .httpVersionNotSupported
  | .unsupportedTransferCoding | .unsupportedMethod => .notImplemented
  | .entityTooLarge => .payloadTooLarge
  | .uriTooLong => .uriTooLong
  | .tooManyHeaders | .headersTooLarge => .requestHeaderFieldsTooLarge
  | _ => .badRequest

/--
An error response the machine writes itself: `status` with `headers`, and its reason phrase as
`text/plain` content (RFC 9110 §15.5, §15.6). A 505 lists the versions the server supports (RFC 9110
§15.6.6).
-/
def errorResponse (status : Status) (headers : Headers := .empty) : Response.Head × ByteArray :=
  let content :=
    match status with
    | .httpVersionNotSupported =>
      "HTTP Version Not Supported: this server supports HTTP/1.0 and HTTP/1.1\n".toUTF8
    | _ => (status.reasonPhrase ++ "\n").toUTF8
  ({ status, headers := headers.insert Header.Name.contentType (.mk "text/plain; charset=utf-8") },
    content)

end Std.Http.Protocol.H1
