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

This module provides types and operations for HTTP/1.1 messages, centered around the abstraction
`Direction`, which indicates whether code is processing incoming requests (server-side, `Direction.receiving`)
or outgoing requests (client-side, `Direction.sending`); the `Message.Head` type is parameterized by
`Direction` and resolves to either `Request.Head` or `Response.Head` accordingly, enabling the writing
of generic code that works uniformly across both client and server message heads while exposing common
operations such as headers, version, and `shouldKeepAlive`, whose behavior adapts based on the chosen direction.
-/

namespace Std.Http.Protocol.H1

set_option linter.all true

/--
Direction of message flow in the HTTP connection in relation with requests.
-/
inductive Direction
  /--
  Processing incoming requests.
  -/
  | receiving

  /--
  Processing outgoing requests.
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

/--
Checks whether the message indicates that the connection should be kept alive.
-/
@[inline]
def Message.Head.shouldKeepAlive (message : Message.Head dir) : Bool :=
  ¬message.headers.hasEntry (.new "connection") (.new "close")
  ∧ message.version = .v11

instance : Repr (Message.Head dir) :=
  match dir with
  | .receiving => inferInstanceAs (Repr Request.Head)
  | .sending => inferInstanceAs (Repr Response.Head)

instance : ToString (Message.Head dir) :=
  match dir with
  | .receiving => inferInstanceAs (ToString Request.Head)
  | .sending => inferInstanceAs (ToString Response.Head)

instance : EmptyCollection (Message.Head dir) where
  emptyCollection :=
    match dir with
    | .receiving => {}
    | .sending => {}

private def isChunked (message : Message.Head dir) : Option Bool :=
  let headers := message.headers

  if let some res := headers.get? (.new "transfer-encoding") then
    let encodings := res.value.split "," |>.toArray.map (·.trimAscii.toString.toLower)
    if encodings.isEmpty then
      none
    else
      let chunkedCount := encodings.filter (· == "chunked") |>.size
      let lastIsChunked := encodings.back? == some "chunked"

      if chunkedCount > 1 then
        none
      else if chunkedCount = 1 ∧ ¬lastIsChunked then
        none
      else
        some lastIsChunked
  else
    some false

/--
Determines the message body size based on the `Content-Length` header and the `Transfer-Encoding` (chunked) flag.
-/
@[inline]
def Message.Head.getSize (message : Message.Head dir) : Option Body.Length :=
  match (message.headers.getAll? (.new "content-length"), isChunked message) with
  | (some #[cl], some false) => .fixed <$> cl.value.toNat?
  | (none, some false) =>some (.fixed 0)
  | (none, some true) => some .chunked
  | (some _, some _) => none -- To avoid request smuggling with multiple content-length headers.
  | (_, none) => none -- Error validating the chunked encoding
