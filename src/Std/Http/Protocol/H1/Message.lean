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
@[expose]
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

  -- Single transfer-encoding header.
  | some #[header] =>
    let te := Header.TransferEncoding.parse header

    match Header.TransferEncoding.isChunked <$> te, contentLength with
    | some true, none =>
        -- HTTP/1.0 does not define chunked transfer encoding (RFC 2068 §19.4.6).
        -- A server MUST NOT use chunked with an HTTP/1.0 peer; likewise, an
        -- HTTP/1.0 request carrying Transfer-Encoding: chunked is malformed.
        if message.version == .v10 then none else some .chunked
    | _, _ => none -- To avoid request smuggling when TE and CL are mixed.

  -- We disallow multiple transfer-encoding headers.
  | some _ => none
/--
Checks whether the message indicates that the connection should be kept alive.
-/
def Message.Head.shouldKeepAlive (message : Message.Head dir) : Bool :=
  let tokens? : Option (Array String) :=
    match message.headers.getAll? .connection with
    | none => some #[]
    | some values =>
        values.foldl (fun acc raw => do
          let acc ← acc
          let parsed ← Header.Connection.parse raw
          pure (acc ++ parsed.tokens)
        ) (some #[])

  match tokens? with
  | none => false
  | some tokens =>
      if message.version == .v11 then
        !tokens.any (· == "close")
      else
        tokens.any (· == "keep-alive")

instance : Repr (Message.Head dir) :=
  match dir with
  | .receiving => inferInstanceAs (Repr Request.Head)
  | .sending => inferInstanceAs (Repr Response.Head)

instance : Internal.Encode .v11 (Message.Head dir) :=
  match dir with
  | .receiving => inferInstanceAs (Internal.Encode .v11 Request.Head)
  | .sending => inferInstanceAs (Internal.Encode .v11 Response.Head)

instance : EmptyCollection (Message.Head dir) where
  emptyCollection :=
    match dir with
    | .receiving => { method := .get, version := .v11 }
    | .sending => {}
