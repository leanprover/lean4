/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Internal.Http.Data

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
  Generating and sending outgoing responses to clients.
  -/
  | sending
deriving BEq

/--
Inverts the direction of the requests.
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
Gets the version of a `Message`.
-/
def Message.Head.version (m : Message.Head dir) : Version :=
  match dir with
  | .receiving => Request.Head.version m
  | .sending => Response.Head.version m

private def isChunked (message : Message.Head dir) : Option Bool :=
  match message.headers.get? .transferEncoding with
  | none => some false
  | some v => Header.TransferEncoding.parse v |>.map (·.isChunked)

/--
Determines the message body size based on the `Content-Length` header and the `Transfer-Encoding` (chunked) flag.
-/
def Message.Head.getSize (message : Message.Head dir) (allowEOFBody : Bool) : Option Body.Length :=
  match (message.headers.getAll? .contentLength, isChunked message) with
  | (some #[cl], some false) => .fixed <$> cl.value.toNat?
  | (none, some false) => if allowEOFBody then some (.fixed 0) else none
  | (none, some true) => some .chunked
  | (some _, some _) => none -- To avoid request smuggling with multiple content-length headers.
  | (_, none) => none -- Error validating the chunked encoding


/--
Checks whether the message indicates that the connection should be kept alive.
-/
@[inline]
def Message.Head.shouldKeepAlive (message : Message.Head dir) : Bool :=
  ¬message.headers.hasEntry .connection (.mk "close")
  ∧ message.version = .v11

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
    | .receiving => {}
    | .sending => {}
