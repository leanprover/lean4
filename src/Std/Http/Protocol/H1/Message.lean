/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
import Init.Data.Array
public import Std.Http.Data

public section

/-!
# Message

This module provides types and operations for HTTP/1.1 messages, centered around the `Direction`
type which models the server's role in message exchange: `Direction.receiving` for parsing incoming
requests from clients, and `Direction.sending` for generating outgoing responses to clients.
The `Message.Head` type is parameterized by `Direction` and resolves to `Request.Head` or
`Response.Head` accordingly, enabling generic code that works uniformly across both phases
while exposing common operations such as headers, version, and `shouldKeepAlive`
-/

namespace Std.Http.Protocol.H1

set_option linter.all true

/--
Direction of message flow from the server's perspective.
-/
inductive Direction
  /--
  Receiving and parsing incoming requests from clients.
  -/
  | receiving

  /--
  Client perspective: writing outgoing requests and reading incoming responses.
  -/
  | sending
deriving BEq

/--
Inverts the message direction.
-/
abbrev Direction.swap : Direction → Direction
  | .receiving => .sending
  | .sending => .receiving

/--
Gets the message head type based on direction.
-/
@[expose]
def Message.Head : Direction → Type
  | .receiving => Request.Head
  | .sending => Response.Head

/--
Gets the headers of a `Message`.
-/
def Message.Head.headers (m : Message.Head dir) : Headers :=
  match dir with
  | .receiving => Request.Head.headers m
  | .sending => Response.Head.headers m

/--
Returns a copy of the message head with the headers replaced.
-/
def Message.Head.setHeaders (m : Message.Head dir) (headers : Headers) : Message.Head dir :=
  match dir with
  | .receiving => { (m : Request.Head)  with headers }
  | .sending   => { (m : Response.Head) with headers }

/--
Gets the version of a `Message`.
-/
def Message.Head.version (m : Message.Head dir) : Version :=
  match dir with
  | .receiving => Request.Head.version m
  | .sending => Response.Head.version m

/--
Determines the message body size based on the `Content-Length` header and the `Transfer-Encoding` (chunked) flag.
-/
def Message.Head.getSize (message : Message.Head dir) (allowEOFBody : Bool) : Option Body.Length :=
  let contentLength := message.headers.getAll? .contentLength

  match message.headers.getAll? .transferEncoding with
  | none =>
      match contentLength with
      | some #[cl] => .fixed <$> (Header.ContentLength.parse cl |>.map (·.length))
      | some _ => none -- To avoid request smuggling with malformed/multiple content-length headers.
      | none => if allowEOFBody then some (.fixed 0) else none

  | some values =>
    match Header.TransferEncoding.finalCodingIsChunked? values, contentLength with
    | some true, none =>
        -- HTTP/1.0 does not define chunked transfer encoding (RFC 2068 §19.4.6).
        -- A server MUST NOT use chunked with an HTTP/1.0 peer; likewise, an
        -- HTTP/1.0 request carrying Transfer-Encoding: chunked is malformed.
        if message.version == .v10 then none else some .chunked
    | _, _ => none -- To avoid request smuggling when TE and CL are mixed.

/--
Checks whether the message indicates that the connection should be kept alive. A `close` option
ends the connection for every version, even next to `keep-alive` (RFC 9112 §9.3, §9.6); otherwise
HTTP/1.1 persists by default and HTTP/1.0 only with `keep-alive`.
-/
def Message.Head.shouldKeepAlive (message : Message.Head dir) : Bool :=
  -- Most messages have no `Connection` field.
  match message.headers.getAll? .connection with
  | none => message.version == .v11
  | some values =>
    match values.mapM Header.Connection.parse with
    | none => false
    | some options =>
      if options.any (·.tokens.contains "close") then
        false
      else
        message.version == .v11 || options.any (·.tokens.contains "keep-alive")

instance : Repr (Message.Head dir) :=
  match dir with
  | .receiving => inferInstanceAs (Repr Request.Head)
  | .sending => inferInstanceAs (Repr Response.Head)

instance : Internal.Encode .v11 (Message.Head dir) :=
  match dir with
  | .receiving => inferInstanceAs (Internal.Encode .v11 Request.Head)
  | .sending => inferInstanceAs (Internal.Encode .v11 Response.Head)

/--
Whether an `Expect` field line lists the expectation `100-continue`, compared case-insensitively. The
line is split at the commas outside quoted strings (RFC 9110 §5.6.1, §5.6.4), so neither a member
with a value (`100-continue=x`) nor one inside a quoted string (`a="b, 100-continue"`) matches.
-/
private def listsContinue (value : String) : Bool :=
  let isContinue (member : String) := member.trimAscii.toString.toLower == "100-continue"
  let (found, last, _, _) := value.foldl (init := (false, "", false, false))
    fun (found, member, quoted, escaped) c =>
      if escaped then (found, member.push c, quoted, false)
      else if quoted && c == '\\' then (found, member.push c, quoted, true)
      else if c == '"' then (found, member.push c, !quoted, false)
      else if c == ',' && !quoted then (found || isContinue member, "", false, false)
      else (found, member.push c, quoted, false)
  found || isContinue last

/--
Returns `true` when the `Expect` field lines, which form one list (RFC 9110 §5.3), have the member
`100-continue` (RFC 9110 §10.1.1). Other expectations are ignored.

RFC 9110 §15.2: Since HTTP/1.0 did not define any 1xx status codes, a server MUST NOT send a 1xx response
to an HTTP/1.0 client.
-/
def Message.Head.hasExpectContinue (message : Message.Head dir) : Bool :=
  if message.version != .v11 then
    false
  else
    match message.headers.getAll? Header.Name.expect with
    | some values => values.any (listsContinue ·.value)
    | none => false

instance : EmptyCollection (Message.Head dir) where
  emptyCollection :=
    match dir with
    | .receiving => { method := .get, version := .v11 }
    | .sending => {}
