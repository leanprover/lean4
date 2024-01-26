/-
Copyright (c) 2021 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Marc Huisinga
-/
import Lean.DeclarationRange

import Lean.Data.Json
import Lean.Data.Lsp

import Lean.Server.FileSource
import Lean.Server.Utils

import Lean.Server.Rpc.Basic

namespace Lean.Server

structure RequestError where
  code    : JsonRpc.ErrorCode
  message : String
  deriving Inhabited

namespace RequestError
open JsonRpc

def fileChanged : RequestError :=
  { code := ErrorCode.contentModified
    message := "File changed." }

def methodNotFound (method : String) : RequestError :=
  { code := ErrorCode.methodNotFound
    message := s!"No request handler found for '{method}'" }

def invalidParams (message : String) : RequestError :=
  {code := ErrorCode.invalidParams, message}

def internalError (message : String) : RequestError :=
  { code := ErrorCode.internalError, message }

def ofException (e : Lean.Exception) : IO RequestError :=
  return internalError (← e.toMessageData.toString)

def ofIoError (e : IO.Error) : RequestError :=
  internalError (toString e)

def toLspResponseError (id : RequestID) (e : RequestError) : ResponseError Unit :=
  { id := id
    code := e.code
    message := e.message }

end RequestError

def parseRequestParams (paramType : Type) [FromJson paramType] (params : Json)
    : Except RequestError paramType :=
  fromJson? params |>.mapError fun inner =>
    { code := JsonRpc.ErrorCode.parseError
      message := s!"Cannot parse request params: {params.compress}\n{inner}" }

variable (InitSnap : Type)

structure RpcSession where
  objects         : RpcObjectStore
  /-- The `IO.monoMsNow` time when the session expires. See `$/lean/rpc/keepAlive`. -/
  expireTime      : Nat

namespace RpcSession

def keepAliveTimeMs : Nat :=
  30000

def new : IO (UInt64 × RpcSession) := do
  /- We generate a random ID to ensure that session IDs do not repeat across re-initializations
  and worker restarts. Otherwise, the client may attempt to use outdated references. -/
  let newId ← ByteArray.toUInt64LE! <$> IO.getRandomBytes 8
  let newSesh := {
    objects := {}
    expireTime := (← IO.monoMsNow) + keepAliveTimeMs
  }
  return (newId, newSesh)

def keptAlive (monoMsNow : Nat) (s : RpcSession) : RpcSession :=
  { s with expireTime := monoMsNow + keepAliveTimeMs }

def hasExpired (s : RpcSession) : IO Bool :=
  return s.expireTime ≤ (← IO.monoMsNow)

end RpcSession

structure RequestContext where
  initSnap      : InitSnap
  rpcSessions   : RBMap UInt64 (IO.Ref RpcSession) compare
  srcSearchPath : SearchPath
  doc           : DocumentMeta
  hLog          : IO.FS.Stream
  initParams    : Lsp.InitializeParams

abbrev RequestTask α := Task (Except RequestError α)
abbrev RequestT m := ReaderT (RequestContext InitSnap) <| ExceptT RequestError m
/-- Workers execute request handlers in this monad. -/
abbrev RequestM InitSnap := ReaderT (RequestContext InitSnap) <| EIO RequestError

variable {InitSnap}

abbrev RequestTask.pure (a : α) : RequestTask α := .pure (.ok a)

instance : MonadLift IO (RequestM InitSnap) where
  monadLift x := do
    match ←  x.toBaseIO with
    | .error e => throw <| RequestError.ofIoError e
    | .ok v => return v

instance : MonadLift (EIO Exception) (RequestM InitSnap) where
  monadLift x := do
    match ←  x.toBaseIO with
    | .error e => throw <| ← RequestError.ofException e
    | .ok v => return v

namespace RequestM

def asTask (t : RequestM InitSnap α) : RequestM InitSnap (RequestTask α) := do
  let rc ← read
  let t ← EIO.asTask <| t.run rc
  return t.map liftExcept

def mapTask (t : Task α) (f : α → RequestM InitSnap β) : RequestM InitSnap (RequestTask β) := do
  let rc ← read
  let t ← EIO.mapTask (f · rc) t
  return t.map liftExcept

def bindTask (t : Task α) (f : α → RequestM InitSnap (RequestTask β)) : RequestM InitSnap (RequestTask β) := do
  let rc ← read
  EIO.bindTask t (f · rc)

def readDoc : RequestM InitSnap DocumentMeta := do
  return (← read).doc

end RequestM

/-! # The global request handlers table

We maintain a global map of LSP request handlers. This allows user code such as plugins
to register its own handlers, for example to support ITP functionality such as goal state
visualization.

For details of how to register one, see `registerLspRequestHandler`. -/
section HandlerTable
open Lsp

variable (InitSnap : Type)

structure RequestHandler where
  fileSource : Json → Except RequestError Lsp.DocumentUri
  handle : Json → RequestM InitSnap (RequestTask Json)

abbrev RequestHandlersRef InitSnap := IO.Ref (PersistentHashMap String (RequestHandler InitSnap))

variable {InitSnap : Type}
variable (requestHandlers : RequestHandlersRef InitSnap)

/-- NB: This method may only be called in `initialize` blocks (user or builtin).

A registration consists of:
- a type of JSON-parsable request data `paramType`
- a `FileSource` instance for it so the system knows where to route requests
- a type of JSON-serializable response data `respType`
- an actual `handler` which runs in the `RequestM InitSnap` monad and is expected
  to produce an asynchronous `RequestTask` which does any waiting/computation

A handler task may be cancelled at any time, so it should check the cancellation token when possible
to handle this cooperatively. Any exceptions thrown in a request handler will be reported to the client
as LSP error responses. -/
def registerLspRequestHandler (method : String)
    paramType [FromJson paramType] [FileSource paramType]
    respType [ToJson respType]
    (handler : paramType → RequestM InitSnap (RequestTask respType)) : IO Unit := do
  if !(← Lean.initializing) then
    throw <| IO.userError s!"Failed to register LSP request handler for '{method}': only possible during initialization"
  if (← requestHandlers.get).contains method then
    throw <| IO.userError s!"Failed to register LSP request handler for '{method}': already registered"
  let fileSource := fun j =>
    parseRequestParams paramType j |>.map Lsp.fileSource
  let handle := fun j => do
    let params ← liftExcept <| parseRequestParams paramType j
    let t ← handler params
    pure <| t.map <| Except.map ToJson.toJson

  requestHandlers.modify fun rhs => rhs.insert method { fileSource, handle }

def lookupLspRequestHandler (method : String) : IO (Option (RequestHandler InitSnap)) :=
  return (← requestHandlers.get).find? method

/-- NB: This method may only be called in `initialize` blocks (user or builtin).

Register another handler to invoke after the last one registered for a method.
At least one handler for the method must have already been registered to perform
chaining.

For more details on the registration of a handler, see `registerLspRequestHandler`. -/
def chainLspRequestHandler (method : String)
    paramType [FromJson paramType]
    respType [FromJson respType] [ToJson respType]
    (handler : paramType → RequestTask respType → RequestM InitSnap (RequestTask respType)) : IO Unit := do
  if !(← Lean.initializing) then
    throw <| IO.userError s!"Failed to chain LSP request handler for '{method}': only possible during initialization"
  if let some oldHandler ← lookupLspRequestHandler requestHandlers method then
    let handle := fun j => do
      let t ← oldHandler.handle j
      let t := t.map fun x => x.bind fun j => FromJson.fromJson? j |>.mapError fun e =>
        .internalError s!"Failed to parse original LSP response for `{method}` when chaining: {e}"
      let params ← liftExcept <| parseRequestParams paramType j
      let t ← handler params t
      pure <| t.map <| Except.map ToJson.toJson

    requestHandlers.modify fun rhs => rhs.insert method {oldHandler with handle}
  else
    throw <| IO.userError s!"Failed to chain LSP request handler for '{method}': no initial handler registered"

def routeLspRequest (method : String) (params : Json) : IO (Except RequestError DocumentUri) := do
  match (← lookupLspRequestHandler requestHandlers method) with
  | none => return Except.error <| RequestError.methodNotFound method
  | some rh => return rh.fileSource params

def handleLspRequest (method : String) (params : Json) : RequestM InitSnap (RequestTask Json) := do
  match (← lookupLspRequestHandler requestHandlers method) with
  | none =>
    throw <| .internalError
      s!"request '{method}' routed through watchdog but unknown in worker; are both using the same plugins?"
  | some rh => rh.handle params

end HandlerTable
end Lean.Server
