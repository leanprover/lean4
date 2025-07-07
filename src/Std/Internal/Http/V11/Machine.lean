/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Internal.Http.Data.Request
import Std.Internal.Http.Data.Response
import Std.Internal.Http.V11.Parser
import Std.Sync

open Std.Internal.Http.Data

namespace Std
namespace Internal
namespace Http
namespace V11

open Parser

deriving instance Repr for ByteArray

inductive Event
  | requestReceived (request : Parser.RequestLine) (headers : Headers)
  | chunkExt (ext : ByteArray)
  | gotData (data : ByteArray)
  | needMoreData
  | readyToRespond
  | failed (s : String)

inductive State : Type
  | needRequestLine : State
  | needHeader : State
  | needChunkedSize : State
  | needChunkedBody : Nat → State
  | needFixedBody : Nat → State
  | readyToResponse : State
deriving Inhabited

structure Connection where
  state : State
  requestLine : RequestLine
  headers : Headers
  buffer : ByteArray.Iterator
  event : Option Event

  sentHead : Bool
  answerBuffer : ByteArray

namespace Connection

def toArray (x : ByteArray.Iterator) :=
  x.array.extract x.idx x.array.size

def feed (conn : Connection) (data : ByteArray) : Connection :=
  let conn := { conn with buffer := (toArray conn.buffer) ++ data |>.iter }

  match conn.state with
  | .needRequestLine =>
    match Parser.parseRequestLine conn.buffer with
    | .success buffer res =>
      { conn with buffer, state := .needHeader, requestLine := res }
    | .error buffer .eof =>
      { conn with buffer, event := some .needMoreData }
    | .error buffer other =>
      { conn with buffer, event := some (.failed (toString other)) }
  | .needHeader =>
    match Parser.parseHeader conn.buffer with
    | .success buffer (some res) =>
      { conn with buffer, state := .needHeader, headers := conn.headers.insert res.name res.value }
    | .success buffer none =>
      if conn.headers.get? "Host" |>.isNone then
        { conn with buffer, event := some (.failed "need host") }
      else if let some "chunked" := conn.headers.get? "Transfer-Encoding" then
        { conn with buffer, state := .needChunkedSize }
      else if let some res := String.toNat? =<< conn.headers.get? "Content-Length" then
        { conn with buffer, state := .needFixedBody res }
      else
        { conn with buffer, event := some (.failed "need content-length or transfer-encoding") }
    | .error buffer .eof =>
      { conn with buffer, event := some .needMoreData }
    | .error buffer other =>
      { conn with buffer, event := some (.failed (toString other)) }
  | .needChunkedSize =>
    match parseChunkSize conn.buffer with
    | .success buffer (size, ext) =>
      let state : State := if size == 0 then .readyToResponse else .needChunkedBody size
      let event := Event.chunkExt <$> ext
      { conn with buffer, event, state }
    | .error buffer .eof =>
      { conn with buffer, event := some .needMoreData }
    | .error buffer other =>
      { conn with buffer, event := some (.failed (toString other)) }
  | .needChunkedBody size =>
    match parseChunkData size conn.buffer with
    | .success buffer body =>
      { conn with buffer, event := some (.gotData body), state := .needChunkedSize }
    | .error buffer .eof =>
      { conn with buffer, event := some .needMoreData }
    | .error buffer other =>
      { conn with buffer, event := some (.failed (toString other)) }
  | .needFixedBody length =>
    match parseFixedBody length conn.buffer with
    | .success buffer body =>
      { conn with buffer, event := some (.gotData body), state := .readyToResponse }
    | .error buffer .eof =>
      { conn with buffer, event := some .needMoreData }
    | .error buffer other =>
      { conn with buffer, event := some (.failed (toString other)) }
  | .readyToResponse => conn

def answer (conn : Connection) (data : Response Unit) : Connection :=
  match conn.state with
  | .readyToResponse => sorry
  | _ => conn
