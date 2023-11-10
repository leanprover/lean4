/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Init.Control
import Init.System.IO
import Lean.Data.RBTree
import Lean.Data.Json

/-! Implementation of JSON-RPC 2.0 (https://www.jsonrpc.org/specification)
for use in the LSP server. -/

namespace Lean.JsonRpc

open Json

/-- In JSON-RPC, each request from the client editor to the language server comes with a
request id so that the corresponding response can be identified or cancelled. -/
inductive RequestID where
  | str (s : String)
  | num (n : JsonNumber)
  | null
  deriving Inhabited, BEq, Ord

instance : OfNat RequestID n := ⟨RequestID.num n⟩

instance : ToString RequestID where
  toString
  | RequestID.str s => s!"\"{s}\""
  | RequestID.num n => toString n
  | RequestID.null => "null"

/-- Error codes defined by
[JSON-RPC](https://www.jsonrpc.org/specification#error_object) and
[LSP](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#errorCodes). -/
inductive ErrorCode where
  /-- Invalid JSON was received by the server. An error occurred on the server while parsing the JSON text. -/
  | parseError
  /-- The JSON sent is not a valid Request object. -/
  | invalidRequest
  /-- The method does not exist / is not available. -/
  | methodNotFound
  /-- Invalid method parameter(s). -/
  | invalidParams
  /-- Internal JSON-RPC error. -/
  | internalError
  /-- Error code indicating that a server received a notification or
  request before the server has received the `initialize` request. -/
  | serverNotInitialized
  | unknownErrorCode
  -- LSP-specific codes below.
  /-- The server detected that the content of a document got
  modified outside normal conditions. A server should
  NOT send this error code if it detects a content change
  in it unprocessed messages. The result even computed
  on an older state might still be useful for the client.

  If a client decides that a result is not of any use anymore
  the client should cancel the request. -/
  | contentModified
  /-- The client has canceled a request and a server as detected the cancel. -/
  | requestCancelled
  -- Lean-specific codes below.
  | rpcNeedsReconnect
  | workerExited
  | workerCrashed
  deriving Inhabited, BEq

instance : FromJson ErrorCode := ⟨fun
  | num (-32700 : Int) => return ErrorCode.parseError
  | num (-32600 : Int) => return ErrorCode.invalidRequest
  | num (-32601 : Int) => return ErrorCode.methodNotFound
  | num (-32602 : Int) => return ErrorCode.invalidParams
  | num (-32603 : Int) => return ErrorCode.internalError
  | num (-32002 : Int) => return ErrorCode.serverNotInitialized
  | num (-32001 : Int) => return ErrorCode.unknownErrorCode
  | num (-32801 : Int) => return ErrorCode.contentModified
  | num (-32800 : Int) => return ErrorCode.requestCancelled
  | num (-32900 : Int) => return ErrorCode.rpcNeedsReconnect
  | num (-32901 : Int) => return ErrorCode.workerExited
  | num (-32902 : Int) => return ErrorCode.workerCrashed
  | _  => throw "expected error code"⟩

instance : ToJson ErrorCode := ⟨fun
  | ErrorCode.parseError           => (-32700 : Int)
  | ErrorCode.invalidRequest       => (-32600 : Int)
  | ErrorCode.methodNotFound       => (-32601 : Int)
  | ErrorCode.invalidParams        => (-32602 : Int)
  | ErrorCode.internalError        => (-32603 : Int)
  | ErrorCode.serverNotInitialized => (-32002 : Int)
  | ErrorCode.unknownErrorCode     => (-32001 : Int)
  | ErrorCode.contentModified      => (-32801 : Int)
  | ErrorCode.requestCancelled     => (-32800 : Int)
  | ErrorCode.rpcNeedsReconnect    => (-32900 : Int)
  | ErrorCode.workerExited         => (-32901 : Int)
  | ErrorCode.workerCrashed        => (-32902 : Int)⟩

/-- A JSON-RPC message.

Uses separate constructors for notifications and errors because client and server
behavior is expected to be wildly different for both.
-/
inductive Message where
  /-- A request message to describe a request between the client and the server. Every processed request must send a response back to the sender of the request. -/
  | request (id : RequestID) (method : String) (params? : Option Structured)
  /-- A notification message. A processed notification message must not send a response back. They work like events. -/
  | notification (method : String) (params? : Option Structured)
  /-- A Response Message sent as a result of a request. -/
  | response (id : RequestID) (result : Json)
  /-- A non-successful response. -/
  | responseError (id : RequestID) (code : ErrorCode) (message : String) (data? : Option Json)

def Batch := Array Message

/-- Generic version of `Message.request`.

A request message to describe a request between the client and the server. Every processed request must send a response back to the sender of the request.

- [LSP](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#requestMessage)
- [JSON-RPC](https://www.jsonrpc.org/specification#request_object)
-/
structure Request (α : Type u) where
  id     : RequestID
  method : String
  param  : α
  deriving Inhabited, BEq

instance [ToJson α] : CoeOut (Request α) Message :=
  ⟨fun r => Message.request r.id r.method (toStructured? r.param).toOption⟩

/-- Generic version of `Message.notification`.

A notification message. A processed notification message must not send a response back. They work like events.

- [JSON-RPC](https://www.jsonrpc.org/specification#notification)
- [LSP](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#notificationMessage).
-/
structure Notification (α : Type u) where
  method : String
  param  : α
  deriving Inhabited, BEq

instance [ToJson α] : CoeOut (Notification α) Message :=
  ⟨fun r => Message.notification r.method (toStructured? r.param).toOption⟩

/-- Generic version of `Message.response`.

A Response Message sent as a result of a request. If a request doesn’t provide a
result value the receiver of a request still needs to return a response message
to conform to the JSON-RPC specification. The result property of the ResponseMessage
should be set to null in this case to signal a successful request.

References:
- [JSON-RPC](https://www.jsonrpc.org/specification#response_object)
- [LSP](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#responseMessage)
-/
structure Response (α : Type u) where
  id     : RequestID
  result : α
  deriving Inhabited, BEq

instance [ToJson α] : CoeOut (Response α) Message :=
  ⟨fun r => Message.response r.id (toJson r.result)⟩

/-- Generic version of `Message.responseError`.

References:
- [JSON-RPC](https://www.jsonrpc.org/specification#error_object)
- [LSP](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#responseError).
-/
structure ResponseError (α : Type u) where
  id      : RequestID
  code    : ErrorCode
  /-- A string providing a short description of the error. -/
  message : String
  /-- A primitive or structured value that contains additional
      information about the error. Can be omitted. -/
  data?   : Option α := none
  deriving Inhabited, BEq

instance [ToJson α] : CoeOut (ResponseError α) Message :=
  ⟨fun r => Message.responseError r.id r.code r.message (r.data?.map toJson)⟩

instance : Coe String RequestID := ⟨RequestID.str⟩
instance : Coe JsonNumber RequestID := ⟨RequestID.num⟩

private def RequestID.lt : RequestID → RequestID → Bool
  | RequestID.str a, RequestID.str b            => a < b
  | RequestID.num a, RequestID.num b            => a < b
  | RequestID.null,  RequestID.num _            => true
  | RequestID.null,  RequestID.str _            => true
  | RequestID.num _, RequestID.str _            => true
  | _, _ /- str < *, num < null, null < null -/ => false

private def RequestID.ltProp : LT RequestID :=
  ⟨fun a b => RequestID.lt a b = true⟩

instance : LT RequestID :=
  RequestID.ltProp

instance (a b : RequestID) : Decidable (a < b) :=
  inferInstanceAs (Decidable (RequestID.lt a b = true))

instance : FromJson RequestID := ⟨fun j =>
  match j with
  | str s => return RequestID.str s
  | num n => return RequestID.num n
  | _     => throw "a request id needs to be a number or a string"⟩

instance : ToJson RequestID := ⟨fun rid =>
  match rid with
  | RequestID.str s => s
  | RequestID.num n => num n
  | RequestID.null  => null⟩

instance : ToJson Message := ⟨fun m =>
  mkObj $ ⟨"jsonrpc", "2.0"⟩ :: match m with
  | Message.request id method params? =>
    [ ⟨"id", toJson id⟩,
      ⟨"method", method⟩
    ] ++ opt "params" params?
  | Message.notification method params? =>
    ⟨"method", method⟩ ::
    opt "params" params?
  | Message.response id result =>
    [ ⟨"id", toJson id⟩,
      ⟨"result", result⟩]
  | Message.responseError id code message data? =>
    [ ⟨"id", toJson id⟩,
      ⟨"error", mkObj $ [
          ⟨"code", toJson code⟩,
          ⟨"message", message⟩
        ] ++ opt "data" data?⟩
    ]⟩

instance : FromJson Message where
  fromJson? j := do
    let "2.0" ← j.getObjVal? "jsonrpc" | throw "only version 2.0 of JSON RPC is supported"
    (do let id ← j.getObjValAs? RequestID "id"
        let method ← j.getObjValAs? String "method"
        let params? := j.getObjValAs? Structured "params"
        pure (Message.request id method params?.toOption)) <|>
    (do let method ← j.getObjValAs? String "method"
        let params? := j.getObjValAs? Structured "params"
        pure (Message.notification method params?.toOption)) <|>
    (do let id ← j.getObjValAs? RequestID "id"
        let result ← j.getObjVal? "result"
        pure (Message.response id result)) <|>
    (do let id ← j.getObjValAs? RequestID "id"
        let err ← j.getObjVal? "error"
        let code ← err.getObjValAs? ErrorCode "code"
        let message ← err.getObjValAs? String "message"
        let data? := err.getObjVal? "data"
        pure (Message.responseError id code message data?.toOption))

-- TODO(WN): temporary until we have deriving FromJson
instance [FromJson α] : FromJson (Notification α) where
  fromJson? j := do
    let msg : Message ← fromJson? j
    if let Message.notification method params? := msg then
      let params := params?
      let param : α ← fromJson? (toJson params)
      pure $ ⟨method, param⟩
    else throw "not a notfication"

end Lean.JsonRpc

namespace IO.FS.Stream

open Lean
open Lean.JsonRpc

section
  def readMessage (h : FS.Stream) (nBytes : Nat) : IO Message := do
    let j ← h.readJson nBytes
    match fromJson? j with
    | Except.ok m => pure m
    | Except.error inner => throw $ userError s!"JSON '{j.compress}' did not have the format of a JSON-RPC message.\n{inner}"

  def readRequestAs (h : FS.Stream) (nBytes : Nat) (expectedMethod : String) (α) [FromJson α] : IO (Request α) := do
    let m ← h.readMessage nBytes
    match m with
    | Message.request id method params? =>
      if method = expectedMethod then
        let j := toJson params?
        match fromJson? j with
        | Except.ok v => pure ⟨id, expectedMethod, v⟩
        | Except.error inner => throw $ userError s!"Unexpected param '{j.compress}' for method '{expectedMethod}'\n{inner}"
      else
        throw $ userError s!"Expected method '{expectedMethod}', got method '{method}'"
    | _ => throw $ userError s!"Expected JSON-RPC request, got: '{(toJson m).compress}'"

  def readNotificationAs (h : FS.Stream) (nBytes : Nat) (expectedMethod : String) (α) [FromJson α] : IO (Notification α) := do
    let m ← h.readMessage nBytes
    match m with
    | Message.notification method params? =>
      if method = expectedMethod then
        let j := toJson params?
        match fromJson? j with
        | Except.ok v => pure ⟨expectedMethod, v⟩
        | Except.error inner => throw $ userError s!"Unexpected param '{j.compress}' for method '{expectedMethod}'\n{inner}"
      else
        throw $ userError s!"Expected method '{expectedMethod}', got method '{method}'"
    | _ => throw $ userError s!"Expected JSON-RPC notification, got: '{(toJson m).compress}'"

  def readResponseAs (h : FS.Stream) (nBytes : Nat) (expectedID : RequestID) (α) [FromJson α] : IO (Response α) := do
    let m ← h.readMessage nBytes
    match m with
    | Message.response id result =>
      if id == expectedID then
        match fromJson? result with
        | Except.ok v => pure ⟨expectedID, v⟩
        | Except.error inner => throw $ userError s!"Unexpected result '{result.compress}'\n{inner}"
      else
        throw $ userError s!"Expected id {expectedID}, got id {id}"
    | _ => throw $ userError s!"Expected JSON-RPC response, got: '{(toJson m).compress}'"
end

section
  variable [ToJson α]

  def writeMessage (h : FS.Stream) (m : Message) : IO Unit :=
    h.writeJson (toJson m)

  def writeRequest (h : FS.Stream) (r : Request α) : IO Unit :=
    h.writeMessage r

  def writeNotification (h : FS.Stream) (n : Notification α) : IO Unit :=
    h.writeMessage n

  def writeResponse (h : FS.Stream) (r : Response α) : IO Unit :=
    h.writeMessage r

  def writeResponseError (h : FS.Stream) (e : ResponseError Unit) : IO Unit :=
    h.writeMessage (Message.responseError e.id e.code e.message none)

  def writeResponseErrorWithData (h : FS.Stream) (e : ResponseError α) : IO Unit :=
    h.writeMessage e
end

end IO.FS.Stream
