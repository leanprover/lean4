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

/--
Determines the message body size based on the `Content-Length` header and the `Transfer-Encoding` (chunked) flag.
-/
def Message.Head.getSize (message : Message.Head dir) (allowEOFBody : Bool) : Option Body.Length :=
  match message.headers.getAll? .contentLength, message.headers.getAll? .transferEncoding with
  | some #[cl], none =>
    .fixed <$> (Header.ContentLength.parse cl).map (·.length)
  | none, some #[te] =>
    (if · then some .chunked else none) =<< (Header.TransferEncoding.parse te).map (·.isChunked)
  | none, none =>
    if allowEOFBody then some (.fixed 0) else none
  | _, _ => none

/--
Checks whether the message indicates that the connection should be kept alive.
-/
@[inline]
def Message.Head.shouldKeepAlive (message : Message.Head dir) : Bool :=
  ¬message.headers.hasEntry .connection (.new "close")
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

  if let some res := headers.get? .transferEncoding then
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
