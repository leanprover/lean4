/-
Copyright (c) 2021 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Marc Huisinga
-/
import Lean.DeclarationRange

import Lean.Data.Json
import Lean.Data.Lsp

import Lean.Server.FileSource
import Lean.Server.FileWorker.Utils

import Lean.Server.Rpc.Basic

/-! We maintain a global map of LSP request handlers. This allows user code such as plugins
to register its own handlers, for example to support ITP functionality such as goal state
visualization.

For details of how to register one, see `registerLspRequestHandler`. -/

namespace Lean.Server

structure RequestError where
  code    : JsonRpc.ErrorCode
  message : String

namespace RequestError
open JsonRpc

def fileChanged : RequestError :=
  { code := ErrorCode.contentModified
    message := "File changed." }

def methodNotFound (method : String) : RequestError :=
  { code := ErrorCode.methodNotFound
    message := s!"No request handler found for '{method}'" }

instance : Coe IO.Error RequestError where
  coe e := { code := ErrorCode.internalError
             message := toString e }

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

structure RequestContext where
  rpcSessions   : Std.RBMap UInt64 (IO.Ref FileWorker.RpcSession) compare
  -- Will be ready when we have at least the header snapshot, so in requests we can usually block on it using `Task.get`.
  srcSearchPath : Task SearchPath
  doc           : FileWorker.EditableDocument
  hLog          : IO.FS.Stream
  initParams    : Lsp.InitializeParams

abbrev RequestTask α := Task (Except RequestError α)
/-- Workers execute request handlers in this monad. -/
abbrev RequestM := ReaderT RequestContext <| EIO RequestError

instance : Inhabited (RequestM α) :=
  ⟨throw ("executing Inhabited instance?!" : RequestError)⟩

instance : MonadLift IO RequestM where
  monadLift x := x.toEIO fun e => (e : RequestError)

namespace RequestM
open FileWorker
open Snapshots

def readDoc : RequestM EditableDocument := fun rc =>
  return rc.doc

def asTask (t : RequestM α) : RequestM (RequestTask α) := fun rc => do
  let t ← EIO.asTask <| t rc
  return t.map liftExcept

def mapTask (t : Task α) (f : α → RequestM β) : RequestM (RequestTask β) := fun rc => do
  let t ← EIO.mapTask (f · rc) t
  return t.map liftExcept

def bindTask (t : Task α) (f : α → RequestM (RequestTask β)) : RequestM (RequestTask β) := fun rc => do
  EIO.bindTask t (f · rc)

def waitFindSnapAux (notFoundX : RequestM α) (x : Snapshot → RequestM α)
    : Except ElabTaskError (Option Snapshot) → RequestM α
  /- The elaboration task that we're waiting for may be aborted if the file contents change.
  In that case, we reply with the `fileChanged` error. Thanks to this, the server doesn't
  get bogged down in requests for an old state of the document. -/
  | Except.error FileWorker.ElabTaskError.aborted =>
    throwThe RequestError RequestError.fileChanged
  | Except.error (FileWorker.ElabTaskError.ioError e) =>
    throw (e : RequestError)
  | Except.ok none => notFoundX
  | Except.ok (some snap) => x snap

/-- Create a task which waits for the first snapshot matching `p`, handles various errors,
and if a matching snapshot was found executes `x` with it. If not found, the task executes
`notFoundX`. -/
def withWaitFindSnap (doc : EditableDocument) (p : Snapshot → Bool)
  (notFoundX : RequestM β)
  (x : Snapshot → RequestM β)
    : RequestM (RequestTask β) := do
  let findTask ← doc.cmdSnaps.waitFind? p
  mapTask findTask <| waitFindSnapAux notFoundX x

/-- See `withWaitFindSnap`. -/
def bindWaitFindSnap (doc : EditableDocument) (p : Snapshot → Bool)
  (notFoundX : RequestM (RequestTask β))
  (x : Snapshot → RequestM (RequestTask β))
    : RequestM (RequestTask β) := do
  let findTask ← doc.cmdSnaps.waitFind? p
  bindTask findTask <| waitFindSnapAux notFoundX x

end RequestM

/- The global request handlers table. -/
section HandlerTable
open Lsp

structure RequestHandler where
  fileSource : Json → Except RequestError Lsp.DocumentUri
  handle : Json → RequestM (RequestTask Json)

builtin_initialize requestHandlers : IO.Ref (Std.PersistentHashMap String RequestHandler) ←
  IO.mkRef {}

/-- NB: This method may only be called in `builtin_initialize` blocks.

A registration consists of:
- a type of JSON-parsable request data `paramType`
- a `FileSource` instance for it so the system knows where to route requests
- a type of JSON-serializable response data `respType`
- an actual `handler` which runs in the `RequestM` monad and is expected
  to produce an asynchronous `RequestTask` which does any waiting/computation

A handler task may be cancelled at any time, so it should check the cancellation token when possible
to handle this cooperatively. Any exceptions thrown in a request handler will be reported to the client
as LSP error responses. -/
def registerLspRequestHandler (method : String)
    paramType [FromJson paramType] [FileSource paramType]
    respType [ToJson respType]
    (handler : paramType → RequestM (RequestTask respType)) : IO Unit := do
  if !(← IO.initializing) then
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

def lookupLspRequestHandler (method : String) : IO (Option RequestHandler) :=
  return (← requestHandlers.get).find? method

/-- NB: This method may only be called in `builtin_initialize` blocks.

Register another handler to invoke after the last one registered for a method.
At least one handler for the method must have already been registered to perform
chaining.

For more details on the registration of a handler, see `registerLspRequestHandler`. -/
def chainLspRequestHandler (method : String)
    paramType [FromJson paramType]
    respType [FromJson respType] [ToJson respType]
    (handler : paramType → RequestTask respType → RequestM (RequestTask respType)) : IO Unit := do
  if !(← IO.initializing) then
    throw <| IO.userError s!"Failed to chain LSP request handler for '{method}': only possible during initialization"
  if let some oldHandler ← lookupLspRequestHandler method then
    let handle := fun j => do
      let t ← oldHandler.handle j
      let t := t.map fun x => x.bind fun j => FromJson.fromJson? j |>.mapError fun e =>
        IO.userError s!"Failed to parse original LSP response for `{method}` when chaining: {e}"
      let params ← liftExcept <| parseRequestParams paramType j
      let t ← handler params t
      pure <| t.map <| Except.map ToJson.toJson

    requestHandlers.modify fun rhs => rhs.insert method {oldHandler with handle}
  else
    throw <| IO.userError s!"Failed to chain LSP request handler for '{method}': no initial handler registered"

def routeLspRequest (method : String) (params : Json) : IO (Except RequestError DocumentUri) := do
  match (← lookupLspRequestHandler method) with
  | none => return Except.error <| RequestError.methodNotFound method
  | some rh => return rh.fileSource params

def handleLspRequest (method : String) (params : Json) : RequestM (RequestTask Json) := do
  match (← lookupLspRequestHandler method) with
  | none => throw (s!"internal server error: request '{method}' routed through watchdog but unknown in worker; are both using the same plugins?" : RequestError)
  | some rh => rh.handle params

end HandlerTable
end Lean.Server
