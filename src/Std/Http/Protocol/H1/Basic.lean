/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Data
public import Std.Http.Internal

public section

/-!
# HTTP/1.1 protocol types

The vocabulary of the HTTP/1.1 machine: which side of the exchange it is on (`Direction`), the head
of the message it reads (`Message.Head`), what it reports (`Event`, `Error`), and what a step or a
body pull returns (`StepResult`, `PulledChunk`).
-/

namespace Std.Http.Protocol.H1

set_option linter.all true

open Std.Http.Internal

/--
Which side of an exchange a machine is on, named by what it does with requests.
-/
inductive Direction
  /--
  A server: receives requests and sends responses.
  -/
  | receiving

  /--
  A client: sends requests and receives responses.
  -/
  | sending
deriving BEq

/--
The other side of the exchange.
-/
abbrev Direction.swap : Direction → Direction
  | .receiving => .sending
  | .sending => .receiving

/--
The head of the messages a machine reads: requests for a server, responses for a client.
-/
@[expose]
def Message.Head : Direction → Type
  | .receiving => Request.Head
  | .sending => Response.Head

/--
The header fields of a message head.
-/
def Message.Head.headers (m : Message.Head dir) : Headers :=
  match dir with
  | .receiving => Request.Head.headers m
  | .sending => Response.Head.headers m

/--
The message head with its header fields replaced.
-/
def Message.Head.setHeaders (m : Message.Head dir) (headers : Headers) : Message.Head dir :=
  match dir with
  | .receiving => { (m : Request.Head) with headers }
  | .sending => { (m : Response.Head) with headers }

/--
The HTTP version of a message head.
-/
def Message.Head.version (m : Message.Head dir) : Version :=
  match dir with
  | .receiving => Request.Head.version m
  | .sending => Response.Head.version m

instance : Repr (Message.Head dir) :=
  match dir with
  | .receiving => inferInstanceAs (Repr Request.Head)
  | .sending => inferInstanceAs (Repr Response.Head)

instance : EmptyCollection (Message.Head dir) where
  emptyCollection :=
    match dir with
    | .receiving => { method := .get, version := .v11 }
    | .sending => {}

/--
Why a machine failed or closed the connection.
-/
inductive Error
  /--
  A body or chunk is over its limit, or the unread input over what the machine buffers (413).
  -/
  | entityTooLarge

  /--
  The request-target is longer than `Config.maxUriLength` (414).
  -/
  | uriTooLong

  /--
  The message is not HTTP/1.0 or HTTP/1.1 (505).
  -/
  | unsupportedVersion

  /--
  A request's transfer coding is neither `chunked` nor in `Config.acceptedTransferCodings` (501).
  -/
  | unsupportedTransferCoding

  /--
  A request's method is a token the server does not recognize (501).
  -/
  | unsupportedMethod

  /--
  The input ended inside a message.
  -/
  | connectionClosed

  /--
  The message is malformed.
  -/
  | badMessage

  /--
  A message has more header fields than `Config.maxHeaders` (431).
  -/
  | tooManyHeaders

  /--
  A message's header fields are longer than `Config.maxHeaderBytes` (431).
  -/
  | headersTooLarge

  /--
  Any other failure, described by `message`.
  -/
  | other (message : String)
deriving Repr, BEq

instance : ToString Error where
  toString
  | .entityTooLarge => "Entity too large"
  | .uriTooLong => "URI too long"
  | .unsupportedVersion => "Unsupported version"
  | .unsupportedTransferCoding => "Unsupported transfer coding"
  | .unsupportedMethod => "Unsupported method"
  | .connectionClosed => "Connection closed"
  | .badMessage => "Bad message"
  | .tooManyHeaders => "Too many headers"
  | .headersTooLarge => "Headers too large"
  | .other msg => s!"Other error: {msg}"

/--
What a machine reports from a step.
-/
inductive Event (dir : Direction)
  /--
  The machine read a message head.
  -/
  | endHeaders (head : Message.Head dir)

  /--
  The machine needs more input, `size` bytes of it when known.
  -/
  | needMoreData (size : Option Nat)

  /--
  The machine failed with `err`.
  -/
  | failed (err : Error)

  /--
  The connection ends.
  -/
  | close

  /--
  The body of the message read ended.
  -/
  | closeBody

  /--
  The machine waits for the message head to send (`Machine.send`).
  -/
  | needAnswer

  /--
  The exchange is over and the next message can be read.
  -/
  | next

  /--
  A request waits for an `Expect: 100-continue` decision (`Machine.canContinue`).
  -/
  | «continue»
deriving Inhabited, Repr

/--
What one step of the machine produced.
-/
structure StepResult (dir : Direction) where
  /--
  The events of the step, in order.
  -/
  events : Array (Event dir) := #[]

  /--
  The bytes to write to the connection.
  -/
  output : ChunkedBuffer := .empty

/--
A body chunk returned by `Machine.pullBody`.
-/
structure PulledChunk where
  /--
  Whether the chunk ends the body.
  -/
  final : Bool

  /--
  Whether the chunk is part of a chunk whose remaining bytes have not arrived yet.
  -/
  incomplete : Bool

  /--
  The data. Chunked framing is removed; other transfer codings, such as the `gzip` of
  `Transfer-Encoding: gzip`, are not decoded.
  -/
  chunk : Chunk

end Std.Http.Protocol.H1
