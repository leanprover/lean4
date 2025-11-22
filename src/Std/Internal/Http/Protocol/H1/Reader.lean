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

namespace Std.Http.Protocol.H1

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
  State waiting for chunk size in chunked transfer encoding.
  -/
  | needChunkedSize : State dir

  /--
  State waiting for chunk body data of specified size.
  -/
  | needChunkedBody : Nat → State dir

  /--
  State waiting for fixed-length body data of specified size.
  -/
  | needFixedBody : Nat → State dir

  /--
  Requires the outgoing message to continue.
  -/
  | requireOutgoing : Body.Length → State dir

  /-
  State that it completed a single request and can go to the next one
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
  Count of messages that this connection already parsed
  -/
  messageCount : Nat := 0

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
If the current input is exhausted, replaces it; otherwise appends.
-/
@[inline]
def feed (data : ByteArray) (reader : Reader dir) : Reader dir :=
  { reader with input :=
    if reader.input.atEnd
      then data.iter
      else { reader.input with array := reader.input.array ++ data } }

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
def addHeader (name : HeaderName) (value : HeaderValue) (reader : Reader dir) : Reader dir :=
  match dir with
  | .sending => { reader with messageHead := { reader.messageHead with headers := reader.messageHead.headers.insert name value } }
  | .receiving => { reader with messageHead := { reader.messageHead with headers := reader.messageHead.headers.insert name value } }

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
    messageHead := {} }

/--
Checks if more input is needed to continue parsing.
-/
@[inline]
def needsMoreInput (reader : Reader dir) : Bool :=
  reader.input.atEnd && !reader.noMoreInput &&
  match reader.state with
  | .complete | .closed | .failed _ => false
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
  { reader with state := .needHeader 0 }

/--
Transitions to the state for reading a fixed-length body.
-/
@[inline]
def startFixedBody (size : Nat) (reader : Reader dir) : Reader dir :=
  { reader with state := .needFixedBody size }

/--
Transitions to the state for reading chunked transfer encoding.
-/
@[inline]
def startChunkedBody (reader : Reader dir) : Reader dir :=
  { reader with state := .needChunkedSize }

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
  match reader.messageHead.headers.get (.new "connection") with
  | some val => let s := val.value.toLower; s == "keep-alive" || s == "keepalive"
  | none => true

end Reader
