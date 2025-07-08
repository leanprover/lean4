/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Internal.Http.Data.Request
import Std.Internal.Http.Data.Response
import Std.Internal.Http.Data.Body
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
  | close
deriving Repr

inductive State : Type
  | needRequestLine : State
  | needHeader : Nat → State
  | needChunkedSize : State
  | needChunkedBody : Nat → State
  | needFixedBody : Nat → State
  | readyToResponse : State
  | awaitingClose : State
  | sendingResponse : State
  | closed
deriving Inhabited, Repr, BEq

structure Connection where
  state : State := .needRequestLine
  requestLine : RequestLine := default
  headers : Headers := .empty
  buffer : ByteArray.Iterator := ByteArray.emptyWithCapacity 4096 |>.iter
  events : Array Event := #[]
  answerBuffer : ByteArray := .emptyWithCapacity 4096
  maxHeaders : Nat := 100

namespace Connection

def toArray (x : ByteArray.Iterator) :=
  x.array.extract x.idx x.array.size

def shouldKeepAlive (conn : Connection) : Bool :=
  match conn.headers.get? "Connection" <&> String.toLower with
  | some "close" => false
  | some "keep-alive" => true
  | none => true
  | _ => false

def addEvent (conn : Connection) (event : Event) : Connection :=
  { conn with events := conn.events.push event }

def clearEvents (conn : Connection) : Connection :=
  { conn with events := #[] }

partial def feedStep (conn : Connection) : Connection :=
  match conn.state with
  | .needRequestLine =>
    match Parser.parseRequestLine conn.buffer with
    | .success buffer res =>
      let conn' := { conn with buffer, state := .needHeader 0, requestLine := res }
      conn'.addEvent (.requestReceived res conn.headers)
    | .error buffer .eof =>
      { conn with buffer, events := conn.events.push .needMoreData }
    | .error buffer other =>
      { conn with buffer, events := conn.events.push (.failed (toString other)) }
  | .needHeader headerCount =>
    if headerCount >= conn.maxHeaders then
      { conn with events := conn.events.push (.failed "too many headers") }
    else
      match Parser.parseHeader conn.buffer with
      | .success buffer (some res) =>
        { conn with buffer, state := .needHeader (headerCount + 1), headers := conn.headers.insert res.name res.value }
      | .success buffer none =>
        if conn.headers.get? "Host" |>.isNone then
          { conn with buffer, events := conn.events.push (.failed "need host") }
        else if let some "chunked" := conn.headers.get? "Transfer-Encoding" then
          { conn with buffer, state := .needChunkedSize }
        else if let some res := String.toNat? =<< conn.headers.get? "Content-Length" then
          let conn := { conn with buffer, state := .needFixedBody res }
          if res == 0 then conn.addEvent .readyToRespond else conn
        else
          let conn := { conn with buffer, state := .readyToResponse }
          conn.addEvent .readyToRespond
      | .error buffer .eof =>
        { conn with buffer, events := conn.events.push .needMoreData }
      | .error buffer other =>
        { conn with buffer, events := conn.events.push (.failed (toString other)) }
  | .needChunkedSize =>
    match parseChunkSize conn.buffer with
    | .success buffer (size, ext) =>
      let state : State := if size == 0 then .readyToResponse else .needChunkedBody size
      let conn' := { conn with buffer, state }
      let conn'' := match ext with
        | some e => conn'.addEvent (.chunkExt e)
        | none => conn'
      if size == 0 then conn''.addEvent .readyToRespond else conn''
    | .error buffer .eof =>
      { conn with buffer, events := conn.events.push .needMoreData }
    | .error buffer other =>
      { conn with buffer, events := conn.events.push (.failed (toString other)) }
  | .needChunkedBody size =>
    match parseChunkData size conn.buffer with
    | .success buffer body =>
      let conn' := { conn with buffer, state := .needChunkedSize }
      conn'.addEvent (.gotData body)
    | .error buffer .eof =>
      { conn with buffer, events := conn.events.push .needMoreData }
    | .error buffer other =>
      { conn with buffer, events := conn.events.push (.failed (toString other)) }
  | .needFixedBody length =>
    match parseFixedBody length conn.buffer with
    | .success buffer body =>
      let conn' := { conn with buffer, state := .readyToResponse }
      let conn'' := conn'.addEvent (.gotData body)
      conn''.addEvent .readyToRespond
    | .error buffer .eof =>
      { conn with buffer, events := conn.events.push .needMoreData }
    | .error buffer other =>
      { conn with buffer, events := conn.events.push (.failed (toString other)) }
  | .readyToResponse => conn
  | .awaitingClose => conn
  | .sendingResponse => conn
  | .closed => conn

def hasBufferData (conn : Connection) : Bool :=
  conn.buffer.idx < conn.buffer.array.size

partial def feedLoop (conn : Connection) : Connection :=
  let oldState := conn.state
  let conn := feedStep conn
  if hasBufferData conn && conn.state != oldState then
    feedLoop conn
  else
    conn

def feed (conn : Connection) (data : ByteArray) : Connection :=
  let conn := { conn with buffer := (toArray conn.buffer) ++ data |>.iter }
  feedLoop conn

def answer (conn : Connection) (response : Response) : Connection :=
  match conn.state with
  | .readyToResponse =>
    let keepAlive := shouldKeepAlive conn

    let connectionHeader := if keepAlive then "keep-alive" else "close"
    let headers := response.headers.insert "Connection" connectionHeader

    match response.body with
    | .bytes data =>
      let headers := headers.insert "Content-Length" (toString data.size)
      let response := { response with headers }

      let newState := if keepAlive then State.needRequestLine else State.awaitingClose
      let fullResponse := (toString response |>.toUTF8) ++ data

      { conn with answerBuffer := conn.answerBuffer ++ fullResponse, state := newState }
    | .zero =>
      let headers := headers.insert "Content-Length" (toString 0)
      let response := { response with headers }

      let newState := if keepAlive then State.needRequestLine else State.awaitingClose
      let fullResponse := (toString response |>.toUTF8)

      { conn with answerBuffer := conn.answerBuffer ++ fullResponse, state := newState }
    | .stream e =>
      let headers := headers.insert "Transfer-Encoding" "chunked"

      let headers :=
        if headers.get? "Content-Type" |>.isNone
          then headers.insert "Content-Type" "application/octet-stream"
          else headers

      let response := { response with headers }
      let fullResponse := toString response |>.toUTF8

      { conn with answerBuffer := conn.answerBuffer ++ fullResponse, state := .sendingResponse }
  | _ => conn

def close (conn : Connection) : Connection :=
  let conn' := { conn with state := .closed }
  conn'.addEvent .close

def getDataToSend (conn : Connection) : ByteArray × Connection :=
  let data := conn.answerBuffer
  let conn' := { conn with answerBuffer := ByteArray.empty }
  (data, conn')

def getEvents (conn : Connection) : Array Event :=
  conn.events

def shouldClose (conn : Connection) : Bool :=
  match conn.state with
  | .awaitingClose => true
  | .closed => true
  | _ => false
