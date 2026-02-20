/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time
public import Std.Internal.Http.Data
public import Std.Internal.Http.Internal
public import Std.Internal.Http.Protocol.H1.Parser
public import Std.Internal.Http.Protocol.H1.Config
public import Std.Internal.Http.Protocol.H1.Message
public import Std.Internal.Http.Protocol.H1.Error

public section

/-!
# HTTP/1.1 Reader

This module defines the reader state machine for parsing incoming HTTP/1.1 messages.
It tracks the parsing state including start line, headers, and body handling for
both fixed-length and chunked transfer encodings.
-/

namespace Std.Http.Protocol.H1

set_option linter.all true

/--
The body-framing sub-state of the `Reader` state machine.
-/
inductive Reader.BodyState where
  /--
  Parse fixed-length body bytes, tracking the number of bytes remaining.
  -/
  | fixed (remaining : Nat)

  /--
  Parse the next chunk-size line in chunked transfer encoding.
  -/
  | chunkedSize

  /--
  Parse chunk data for the current chunk.
  -/
  | chunkedBody (ext : Array (ExtensionName × Option String)) (remaining : Nat)

  /--
  Parse body bytes until EOF (connection close).
  -/
  | closeDelimited
deriving Inhabited, Repr, BEq

/--
The state of the `Reader` state machine.
-/
inductive Reader.State (dir : Direction) : Type
  /--
  Initial state waiting for HTTP start line.
  -/
  | needStartLine : State dir

  /--
  State waiting for HTTP headers, tracking number of headers parsed.
  -/
  | needHeader : Nat → State dir

  /--
  Unified body-reading state.
  -/
  | readBody : Reader.BodyState → State dir

  /--
  Paused waiting for a `canContinue` decision, carrying the next state.
  -/
  | continue : State dir → State dir

  /--
  State that it completed a single request or response and can go to the next one
  -/
  | complete

  /--
  State that it has completed and cannot process more data.
  -/
  | closed

  /--
  The input is malformed.
  -/
  | failed (error : Error) : State dir
deriving Inhabited, Repr, BEq

/--
Manages the reading state of the HTTP parsing and processing machine.
-/
structure Reader (dir : Direction) where
  /--
  The current state of the machine.
  -/
  state : Reader.State dir := .needStartLine

  /--
  The input byte array.
  -/
  input : ByteArray.Iterator := ByteArray.emptyWithCapacity 4096 |>.iter

  /--
  The incoming message head.
  -/
  messageHead : Message.Head dir := {}

  /--
  Count of messages that this connection has already parsed.
  -/
  messageCount : Nat := 0

  /--
  Number of body bytes read for the current message.
  -/
  bodyBytesRead : Nat := 0

  /--
  Number of header bytes accumulated for the current message.
  Counts name + value bytes plus 4 bytes per line for `: ` and `\r\n`.
  -/
  headerBytesRead : Nat := 0

  /--
  Flag that says that it cannot receive more input (the socket disconnected).
  -/
  noMoreInput : Bool := false

namespace Reader

/--
Checks if the reader is in a closed state and cannot process more messages.
-/
@[inline]
def isClosed (reader : Reader dir) : Bool :=
  match reader.state with
  | .closed => true
  | _ => false

/--
Checks if the reader has completed parsing the current message.
-/
@[inline]
def isComplete (reader : Reader dir) : Bool :=
  match reader.state with
  | .complete => true
  | _ => false

/--
Checks if the reader has encountered an error.
-/
@[inline]
def hasFailed (reader : Reader dir) : Bool :=
  match reader.state with
  | .failed _ => true
  | _ => false

/--
Feeds new data into the reader's input buffer.
If the current input is exhausted, replaces it; otherwise compacts the buffer
by discarding already-parsed bytes before appending.
-/
@[inline]
def feed (data : ByteArray) (reader : Reader dir) : Reader dir :=
  { reader with input :=
    if reader.input.atEnd
      then data.iter
      else (reader.input.array.extract reader.input.pos reader.input.array.size ++ data).iter }

/--
Replaces the reader's input iterator with a new one.
-/
@[inline]
def setInput (input : ByteArray.Iterator) (reader : Reader dir) : Reader dir :=
  { reader with input }

/--
Updates the message head being constructed.
-/
@[inline]
def setMessageHead (messageHead : Message.Head dir) (reader : Reader dir) : Reader dir :=
  { reader with messageHead }

/--
Adds a header to the current message head.
-/
@[inline]
def addHeader (name : Header.Name) (value : Header.Value) (reader : Reader dir) : Reader dir :=
  match dir with
  | .sending | .receiving => { reader with messageHead := { reader.messageHead with headers := reader.messageHead.headers.insert name value } }

/--
Closes the reader, transitioning to the closed state.
-/
@[inline]
def close (reader : Reader dir) : Reader dir :=
  { reader with state := .closed, noMoreInput := true }

/--
Marks the current message as complete and prepares for the next message.
-/
@[inline]
def markComplete (reader : Reader dir) : Reader dir :=
  { reader with
    state := .complete
    messageCount := reader.messageCount + 1 }

/--
Transitions the reader to a failed state with the given error.
-/
@[inline]
def fail (error : Error) (reader : Reader dir) : Reader dir :=
  { reader with state := .failed error }

/--
Resets the reader to parse a new message on the same connection.
-/
@[inline]
def reset (reader : Reader dir) : Reader dir :=
  { reader with
    state := .needStartLine
    bodyBytesRead := 0
    headerBytesRead := 0
    messageHead := {} }

/--
Checks if more input is needed to continue parsing.
-/
@[inline]
def needsMoreInput (reader : Reader dir) : Bool :=
  reader.input.atEnd && !reader.noMoreInput &&
  match reader.state with
  | .complete | .closed | .failed _ | .«continue» _ => false
  | _ => true

/--
Returns the current parse error if the reader has failed.
-/
@[inline]
def getError (reader : Reader dir) : Option Error :=
  match reader.state with
  | .failed err => some err
  | _ => none

/--
Gets the number of bytes remaining in the input buffer.
-/
@[inline]
def remainingBytes (reader : Reader dir) : Nat :=
  reader.input.array.size - reader.input.pos

/--
Advances the input iterator by n bytes.
-/
@[inline]
def advance (n : Nat) (reader : Reader dir) : Reader dir :=
  { reader with input := reader.input.forward n }

/--
Transitions to the state for reading headers.
-/
@[inline]
def startHeaders (reader : Reader dir) : Reader dir :=
  { reader with state := .needHeader 0, bodyBytesRead := 0, headerBytesRead := 0 }

/--
Adds body bytes parsed for the current message.
-/
@[inline]
def addBodyBytes (n : Nat) (reader : Reader dir) : Reader dir :=
  { reader with bodyBytesRead := reader.bodyBytesRead + n }

/--
Adds header bytes accumulated for the current message.
-/
@[inline]
def addHeaderBytes (n : Nat) (reader : Reader dir) : Reader dir :=
  { reader with headerBytesRead := reader.headerBytesRead + n }

/--
Transitions to the state for reading a fixed-length body.
-/
@[inline]
def startFixedBody (size : Nat) (reader : Reader dir) : Reader dir :=
  { reader with state := .readBody (.fixed size) }

/--
Transitions to the state for reading chunked transfer encoding.
-/
@[inline]
def startChunkedBody (reader : Reader dir) : Reader dir :=
  { reader with state := .readBody .chunkedSize }

/--
Marks that no more input will be provided (connection closed).
-/
@[inline]
def markNoMoreInput (reader : Reader dir) : Reader dir :=
  { reader with noMoreInput := true }

/--
Checks if the connection should be kept alive for the next message.
-/
def shouldKeepAlive (reader : Reader dir) : Bool :=
  reader.messageHead.shouldKeepAlive

end Reader
