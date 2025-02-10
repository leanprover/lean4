/-
Copyright (c) 2021 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Marc Huisinga
-/
prelude
import Lean.DeclarationRange

import Lean.Data.Json
import Lean.Data.Lsp
import Lean.Elab.Command

import Lean.Server.FileSource
import Lean.Server.FileWorker.Utils

import Lean.Server.Rpc.Basic

import Std.Sync.Mutex

namespace Lean.Language

/--
Finds the first (in pre-order) snapshot task in `tree` whose `range?` contains `pos` and which
contains an info tree, and then returns that info tree, waiting for any snapshot tasks on the way.
Subtrees that do not contain the position are skipped without forcing their tasks.
-/
partial def SnapshotTree.findInfoTreeAtPos (tree : SnapshotTree) (pos : String.Pos) :
    Task (Option Elab.InfoTree) :=
  goSeq tree.children.toList
where
  goSeq
    | [] => .pure none
    | t::ts =>
      if t.range?.any (·.contains pos) then
        t.task.bind (sync := true) fun tree => Id.run do
          if let some infoTree := tree.element.infoTree? then
            return .pure infoTree
          tree.findInfoTreeAtPos pos |>.bind (sync := true) fun
            | some infoTree => .pure (some infoTree)
            | none => goSeq ts
      else
        goSeq ts

end Lean.Language

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

def requestCancelled : RequestError :=
  { code := ErrorCode.requestCancelled, message := "" }

def ofException (e : Lean.Exception) : IO RequestError :=
  return internalError (← e.toMessageData.toString)

def ofIoError (e : IO.Error) : RequestError :=
  internalError (toString e)

def toLspResponseError (id : RequestID) (e : RequestError) : ResponseError Unit :=
  { id := id
    code := e.code
    message := e.message }

end RequestError

inductive RequestCancellationCause where
  | cancelRequest
  | edit
  deriving Inhabited, BEq

structure RequestCancellationToken where
  promise : IO.Promise RequestCancellationCause

namespace RequestCancellationToken

def new : IO RequestCancellationToken := do
  return { promise := ← IO.Promise.new }

def cancel (tk : RequestCancellationToken) (cause : RequestCancellationCause) : IO Unit :=
  tk.promise.resolve cause

def task (tk : RequestCancellationToken) : Task RequestCancellationCause :=
  tk.promise.result!

def truncatedTask (tk : RequestCancellationToken) : Task Unit :=
  tk.task.map (sync := true) fun _ => ()

def cancelled? (tk : RequestCancellationToken) : IO (Option RequestCancellationCause) := do
  let t := tk.task
  if ← IO.hasFinished t then
    return some t.get
  else
    return none

def wasCancelledByCancelRequest (tk : RequestCancellationToken) : IO Bool := do
  let some c ← tk.cancelled?
    | return false
  return c matches .cancelRequest

def wasCancelledByEdit (tk : RequestCancellationToken) : IO Bool := do
  let some c ← tk.cancelled?
    | return false
  return c matches .edit

end RequestCancellationToken

def parseRequestParams (paramType : Type) [FromJson paramType] (params : Json)
    : Except RequestError paramType :=
  fromJson? params |>.mapError fun inner =>
    { code := JsonRpc.ErrorCode.parseError
      message := s!"Cannot parse request params: {params.compress}\n{inner}" }

structure RequestContext where
  rpcSessions   : RBMap UInt64 (IO.Ref FileWorker.RpcSession) compare
  srcSearchPath : SearchPath
  doc           : FileWorker.EditableDocument
  hLog          : IO.FS.Stream
  initParams    : Lsp.InitializeParams
  cancelTk      : RequestCancellationToken

abbrev RequestTask α := Task (Except RequestError α)
abbrev RequestT m := ReaderT RequestContext <| ExceptT RequestError m
/-- Workers execute request handlers in this monad. -/
abbrev RequestM := ReaderT RequestContext <| EIO RequestError

abbrev RequestTask.pure (a : α) : RequestTask α := Task.pure (.ok a)

instance : MonadLift IO RequestM where
  monadLift x := do
    match ←  x.toBaseIO with
    | .error e => throw <| RequestError.ofIoError e
    | .ok v => return v

instance : MonadLift (EIO Exception) RequestM where
  monadLift x := do
    match ←  x.toBaseIO with
    | .error e => throw <| ← RequestError.ofException e
    | .ok v => return v

namespace RequestM
open FileWorker
open Snapshots

def runInIO (x : RequestM α) (ctx : RequestContext) : IO α := do
  x.run ctx |>.adaptExcept (IO.userError ·.message)

def readDoc [Monad m] [MonadReaderOf RequestContext m] : m EditableDocument := do
  let rc ← readThe RequestContext
  return rc.doc

def asTask (t : RequestM α) : RequestM (RequestTask α) := do
  let rc ← readThe RequestContext
  EIO.asTask <| t.run rc

def mapTask (t : Task α) (f : α → RequestM β) : RequestM (RequestTask β) := do
  let rc ← readThe RequestContext
  EIO.mapTask (f · rc) t

def bindTask (t : Task α) (f : α → RequestM (RequestTask β)) : RequestM (RequestTask β) := do
  let rc ← readThe RequestContext
  EIO.bindTask t (f · rc)

def checkCanceled : RequestM Unit := do
  let rc ← readThe RequestContext
  if ← rc.cancelTk.wasCancelledByCancelRequest then
    throw .requestCancelled

def waitFindSnapAux (notFoundX : RequestM α) (x : Snapshot → RequestM α)
    : Except IO.Error (Option Snapshot) → RequestM α
  /- The elaboration task that we're waiting for may be aborted if the file contents change.
  In that case, we reply with the `fileChanged` error by default. Thanks to this, the server doesn't
  get bogged down in requests for an old state of the document. -/
  | Except.error e => throw (RequestError.ofIoError e)
  | Except.ok none => notFoundX
  | Except.ok (some snap) => x snap

/-- Create a task which waits for the first snapshot matching `p`, handles various errors,
and if a matching snapshot was found executes `x` with it. If not found, the task executes
`notFoundX`. -/
def withWaitFindSnap (doc : EditableDocument) (p : Snapshot → Bool)
    (notFoundX : RequestM β)
    (x : Snapshot → RequestM β)
    : RequestM (RequestTask β) := do
  let findTask := doc.cmdSnaps.waitFind? p
  mapTask findTask <| waitFindSnapAux notFoundX x

/-- See `withWaitFindSnap`. -/
def bindWaitFindSnap (doc : EditableDocument) (p : Snapshot → Bool)
    (notFoundX : RequestM (RequestTask β))
    (x : Snapshot → RequestM (RequestTask β))
    : RequestM (RequestTask β) := do
  let findTask := doc.cmdSnaps.waitFind? p
  bindTask findTask <| waitFindSnapAux notFoundX x

/-- Create a task which waits for the snapshot containing `lspPos` and executes `f` with it.
If no such snapshot exists, the request fails with an error. -/
def withWaitFindSnapAtPos
    (lspPos : Lsp.Position)
    (f : Snapshots.Snapshot → RequestM α)
    : RequestM (RequestTask α) := do
  let doc ← readDoc
  let pos := doc.meta.text.lspPosToUtf8Pos lspPos
  withWaitFindSnap doc (fun s => s.endPos >= pos)
    (notFoundX := throw ⟨.invalidParams, s!"no snapshot found at {lspPos}"⟩)
    (x := f)

open Language.Lean in
/-- Finds the first `CommandParsedSnapshot` fulfilling `p`, asynchronously. -/
partial def findCmdParsedSnap (doc : EditableDocument) (p : CommandParsedSnapshot → Bool) :
    Task (Option CommandParsedSnapshot) := Id.run do
  let some headerParsed := doc.initSnap.result?
    | .pure none
  headerParsed.processedSnap.task.bind (sync := true) fun headerProcessed => Id.run do
    let some headerSuccess := headerProcessed.result?
      | return .pure none
    headerSuccess.firstCmdSnap.task.bind (sync := true) go
where
  go cmdParsed :=
    if p cmdParsed then
      .pure (some cmdParsed)
    else
      match cmdParsed.nextCmdSnap? with
      | some next => next.task.bind (sync := true) go
      | none => .pure none

open Language in
/--
Finds the info tree of the first snapshot task matching `isMatchingSnapshot` and containing `pos`,
asynchronously. The info tree may be from a nested snapshot, such as a single tactic.

See `SnapshotTree.findInfoTreeAtPos` for details on how the search is done.
-/
partial def findInfoTreeAtPos
    (doc : EditableDocument)
    (isMatchingSnapshot : Lean.CommandParsedSnapshot → Bool)
    (pos : String.Pos)
    : Task (Option Elab.InfoTree) :=
  findCmdParsedSnap doc (isMatchingSnapshot ·) |>.bind (sync := true) fun
    | some cmdParsed => toSnapshotTree cmdParsed |>.findInfoTreeAtPos pos |>.bind (sync := true) fun
      | some infoTree => .pure <| some infoTree
      | none          => cmdParsed.finishedSnap.task.map (sync := true) fun s =>
        -- the parser returns exactly one command per snapshot, and the elaborator creates exactly one node per command
        assert! s.cmdState.infoState.trees.size == 1
        some s.cmdState.infoState.trees[0]!
    | none => .pure none

open Language in
/--
Finds the command syntax and info tree of the first snapshot task matching `isMatchingSnapshot` and
containing `pos`, asynchronously. The info tree may be from a nested snapshot,
such as a single tactic.

See `SnapshotTree.findInfoTreeAtPos` for details on how the search is done.
-/
def findCmdDataAtPos
    (doc : EditableDocument)
    (isMatchingSnapshot : Lean.CommandParsedSnapshot → Bool)
    (pos : String.Pos)
    : Task (Option (Syntax × Elab.InfoTree)) :=
  findCmdParsedSnap doc (isMatchingSnapshot ·) |>.bind (sync := true) fun
    | some cmdParsed => toSnapshotTree cmdParsed |>.findInfoTreeAtPos pos |>.bind (sync := true) fun
      | some infoTree => .pure <| some (cmdParsed.stx, infoTree)
      | none          => cmdParsed.finishedSnap.task.map (sync := true) fun s =>
        -- the parser returns exactly one command per snapshot, and the elaborator creates exactly one node per command
        assert! s.cmdState.infoState.trees.size == 1
        some (cmdParsed.stx, s.cmdState.infoState.trees[0]!)
    | none => .pure none

/--
Finds the info tree of the first snapshot task containing `pos` (including trailing whitespace),
asynchronously. The info tree may be from a nested snapshot, such as a single tactic.

See `SnapshotTree.findInfoTreeAtPos` for details on how the search is done.
-/
def findInfoTreeAtPosWithTrailingWhitespace
    (doc : EditableDocument)
    (pos : String.Pos)
    : Task (Option Elab.InfoTree) :=
  -- NOTE: use `>=` since the cursor can be *after* the input (and there is no interesting info on
  -- the first character of the subsequent command if any)
  findInfoTreeAtPos doc (·.parserState.pos ≥ pos) pos

open Elab.Command in
def runCommandElabM (snap : Snapshot) (c : RequestT CommandElabM α) : RequestM α := do
  let rc ← readThe RequestContext
  match ← snap.runCommandElabM rc.doc.meta (c.run rc) with
  | .ok v => return v
  | .error e => throw e

def runCoreM (snap : Snapshot) (c : RequestT CoreM α) : RequestM α := do
  let rc ← readThe RequestContext
  match ← snap.runCoreM rc.doc.meta (c.run rc) with
  | .ok v => return v
  | .error e => throw e

open Elab.Term in
def runTermElabM (snap : Snapshot) (c : RequestT TermElabM α) : RequestM α := do
  let rc ← readThe RequestContext
  match ← snap.runTermElabM rc.doc.meta (c.run rc) with
  | .ok v => return v
  | .error e => throw e

end RequestM

/-! # The global request handlers table

We maintain a global map of LSP request handlers. This allows user code such as plugins
to register its own handlers, for example to support ITP functionality such as goal state
visualization.

For details of how to register one, see `registerLspRequestHandler`. -/
section HandlerTable
open Lsp

structure RequestHandler where
  fileSource : Json → Except RequestError Lsp.DocumentUri
  handle : Json → RequestM (RequestTask Json)

builtin_initialize requestHandlers : IO.Ref (PersistentHashMap String RequestHandler) ←
  IO.mkRef {}

/-- NB: This method may only be called in `initialize` blocks (user or builtin).

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

def lookupLspRequestHandler (method : String) : IO (Option RequestHandler) :=
  return (← requestHandlers.get).find? method

/-- NB: This method may only be called in `initialize` blocks (user or builtin).

Register another handler to invoke after the last one registered for a method.
At least one handler for the method must have already been registered to perform
chaining.

For more details on the registration of a handler, see `registerLspRequestHandler`. -/
def chainLspRequestHandler (method : String)
    paramType [FromJson paramType]
    respType [FromJson respType] [ToJson respType]
    (handler : paramType → RequestTask respType → RequestM (RequestTask respType)) : IO Unit := do
  if !(← Lean.initializing) then
    throw <| IO.userError s!"Failed to chain LSP request handler for '{method}': only possible during initialization"
  if let some oldHandler ← lookupLspRequestHandler method then
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

inductive RequestHandlerCompleteness where
  | complete
  /--
  A request handler is partial if the LSP spec states that the request method implemented by
  the handler should be responded to with the full state of the document, but our implementation
  of the handler only returns a partial result for the document
  (e.g. only for the processed regions of the document, to reduce latency after a `didChange`).
  A request handler can only be partial if LSP also specifies a corresponding `refresh`
  server-to-client request, e.g. `workspace/inlayHint/refresh` for `textDocument/inlayHint`.
  This is necessary because we use the `refresh` request to prompt the client to re-request the
  data for a partial request if we returned a partial response for that request in the past,
  so that the client eventually converges to a complete set of information for the full document.
  -/
  | «partial» (refreshMethod : String) (refreshIntervalMs : Nat)

structure LspResponse (α : Type) where
  response   : α
  isComplete : Bool

structure StatefulRequestHandler where
  fileSource      : Json → Except RequestError Lsp.DocumentUri
  /--
  `handle` with explicit state management for chaining request handlers.
  This function is pure w.r.t. `lastTaskMutex` and `stateRef`, but not `RequestM`.
  -/
  pureHandle      : Json → Dynamic → RequestM (LspResponse Json × Dynamic)
  handle          : Json → RequestM (RequestTask (LspResponse Json))
  /--
  `onDidChange` with explicit state management for chaining request handlers.
  This function is pure w.r.t. `lastTaskMutex` and `stateRef`, but not `RequestM`.
  -/
  pureOnDidChange : DidChangeTextDocumentParams → (StateT Dynamic RequestM) Unit
  onDidChange     : DidChangeTextDocumentParams → RequestM Unit
  lastTaskMutex   : Std.Mutex (Task Unit)
  initState       : Dynamic
  /--
  `stateRef` is synchronized in `registerStatefulLspRequestHandler` by using `lastTaskMutex` to
  ensure that stateful request tasks for the same handler are executed sequentially (in order of arrival).
  -/
  stateRef        : IO.Ref Dynamic
  completeness    : RequestHandlerCompleteness

builtin_initialize statefulRequestHandlers : IO.Ref (PersistentHashMap String StatefulRequestHandler) ←
  IO.mkRef {}

private def getState! (method : String) (state : Dynamic) stateType [TypeName stateType] : RequestM stateType := do
  let some state := state.get? stateType
    | throw <| .internalError s!"Got invalid state type in stateful LSP request handler for {method}"
  return state

private def getIOState! (method : String) (state : Dynamic) stateType [TypeName stateType] : IO stateType := do
  let some state := state.get? stateType
    | throw <| .userError s!"Got invalid state type in stateful LSP request handler for {method}"
  return state

private def overrideStatefulLspRequestHandler
    (method : String) (completeness : RequestHandlerCompleteness)
    paramType [FromJson paramType] [FileSource paramType]
    respType [ToJson respType]
    stateType [TypeName stateType]
    (initState : stateType)
    (handler : paramType → stateType → RequestM (LspResponse respType × stateType))
    (onDidChange : DidChangeTextDocumentParams → StateT stateType RequestM Unit)
    : IO Unit := do
  if !(← Lean.initializing) then
    throw <| IO.userError s!"Failed to register stateful LSP request handler for '{method}': only possible during initialization"
  let fileSource := fun j =>
    parseRequestParams paramType j |>.map Lsp.fileSource
  let lastTaskMutex ← Std.Mutex.new <| Task.pure ()
  let initState := Dynamic.mk initState
  let stateRef ← IO.mkRef initState

  let pureHandle : Json → Dynamic → RequestM (LspResponse Json × Dynamic) := fun param state => do
    let param ← liftExcept <| parseRequestParams paramType param
    let state ← getState! method state stateType
    let (r, state') ← handler param state
    return ({ r with response := toJson r.response }, Dynamic.mk state')

  let handle : Json → RequestM (RequestTask (LspResponse Json)) := fun param => lastTaskMutex.atomically do
    let lastTask ← get
    let requestTask ← RequestM.mapTask lastTask fun () => do
      let state ← stateRef.get
      let (r, state') ← pureHandle param state
      stateRef.set state'
      return r
    set <| requestTask.map <| fun _ => ()
    return requestTask

  let pureOnDidChange : DidChangeTextDocumentParams → (StateT Dynamic RequestM) Unit := fun param => do
    let state ← getState! method (← get) stateType
    let ((), state') ← onDidChange param |>.run state
    set <| Dynamic.mk state'

  let onDidChange : DidChangeTextDocumentParams → RequestM Unit := fun param => lastTaskMutex.atomically do
      let lastTask ← get
      let didChangeTask ← RequestM.mapTask (t := lastTask) fun () => do
        let state ← stateRef.get
        let ((), state') ← pureOnDidChange param |>.run state
        stateRef.set state'
      set <| didChangeTask.map <| fun _ => ()

  statefulRequestHandlers.modify fun rhs => rhs.insert method {
    fileSource,
    pureHandle,
    handle,
    pureOnDidChange,
    onDidChange,
    lastTaskMutex,
    initState,
    stateRef,
    completeness
  }

private def registerStatefulLspRequestHandler
    (method : String) (completeness : RequestHandlerCompleteness)
    paramType [FromJson paramType] [FileSource paramType]
    respType [ToJson respType]
    stateType [TypeName stateType]
    (initState : stateType)
    (handler : paramType → stateType → RequestM (LspResponse respType × stateType))
    (onDidChange : DidChangeTextDocumentParams → StateT stateType RequestM Unit)
    : IO Unit := do
  if (← requestHandlers.get).contains method then
    throw <| IO.userError s!"Failed to register stateful LSP request handler for '{method}': already registered"
  overrideStatefulLspRequestHandler method completeness paramType respType stateType initState handler onDidChange

def registerCompleteStatefulLspRequestHandler (method : String)
    paramType [FromJson paramType] [FileSource paramType]
    respType [ToJson respType]
    stateType [TypeName stateType]
    (initState : stateType)
    (handler : paramType → stateType → RequestM (respType × stateType))
    (onDidChange : DidChangeTextDocumentParams → StateT stateType RequestM Unit)
    : IO Unit :=
  let handler : paramType → stateType → RequestM (LspResponse respType × stateType) := fun p s => do
    let (response, s) ← handler p s
    return ({ response, isComplete := true }, s)
  registerStatefulLspRequestHandler method .complete paramType respType stateType initState handler onDidChange

def registerPartialStatefulLspRequestHandler (method refreshMethod : String) (refreshIntervalMs : Nat)
    paramType [FromJson paramType] [FileSource paramType]
    respType [ToJson respType]
    stateType [TypeName stateType]
    (initState : stateType)
    (handler : paramType → stateType → RequestM (LspResponse respType × stateType))
    (onDidChange : DidChangeTextDocumentParams → StateT stateType RequestM Unit) :=
  registerStatefulLspRequestHandler method (.partial refreshMethod refreshIntervalMs) paramType respType stateType initState handler onDidChange

def isStatefulLspRequestMethod (method : String) : BaseIO Bool := do
  return (← statefulRequestHandlers.get).contains method

def lookupStatefulLspRequestHandler (method : String) : BaseIO (Option StatefulRequestHandler) := do
  return (← statefulRequestHandlers.get).find? method

def partialLspRequestHandlerMethods : IO (Array (String × String × Nat)) := do
  return (← statefulRequestHandlers.get).toArray.filterMap fun (method, h) => do
    let .partial refreshMethod refreshIntervalMs := h.completeness
      | none
    return (method, refreshMethod, refreshIntervalMs)

def chainStatefulLspRequestHandler (method : String)
    paramType [FromJson paramType] [ToJson paramType] [FileSource paramType]
    respType [FromJson respType] [ToJson respType]
    stateType [TypeName stateType]
    (handler : paramType → LspResponse respType → stateType → RequestM (LspResponse respType × stateType))
    (onDidChange : DidChangeTextDocumentParams → StateT stateType RequestM Unit) : IO Unit := do
  if ! (← Lean.initializing) then
    throw <| IO.userError s!"Failed to chain stateful LSP request handler for '{method}': only possible during initialization"
  let some oldHandler ← lookupStatefulLspRequestHandler method
    | throw <| IO.userError s!"Failed to chain stateful LSP request handler for '{method}': no initial handler registered"
  let oldHandle := oldHandler.pureHandle
  let oldOnDidChange := oldHandler.pureOnDidChange
  let initState ← getIOState! method oldHandler.initState stateType
  let handle (p : paramType) (s : stateType) : RequestM (LspResponse respType × stateType) := do
    let (r, s) ← oldHandle (toJson p) (Dynamic.mk s)
    let .ok response := fromJson? r.response
      | throw <| RequestError.internalError "Failed to convert response of previous request handler when chaining stateful LSP request handlers"
    let r := { r with response := response }
    let s ← getState! method s stateType
    handler p r s
  let onDidChange (p : DidChangeTextDocumentParams) : StateT stateType RequestM Unit := do
    let s ← get
    let ((), s) ← oldOnDidChange p |>.run (Dynamic.mk s)
    let s ← getState! method s stateType
    let ((), s) ← onDidChange p |>.run s
    set <| s
  overrideStatefulLspRequestHandler method oldHandler.completeness paramType respType stateType initState
    handle onDidChange

def handleOnDidChange (p : DidChangeTextDocumentParams) : RequestM Unit := do
  (← statefulRequestHandlers.get).forM fun _ handler => do
    handler.onDidChange p

def handleLspRequest (method : String) (params : Json) : RequestM (RequestTask (LspResponse Json)) := do
  if ← isStatefulLspRequestMethod method then
    match ← lookupStatefulLspRequestHandler method with
    | none =>
      throw <| .internalError
        s!"request '{method}' routed through watchdog but unknown in worker; are both using the same plugins?"
    | some rh => rh.handle params
  else
    match ← lookupLspRequestHandler method with
    | none =>
      throw <| .internalError
        s!"request '{method}' routed through watchdog but unknown in worker; are both using the same plugins?"
    | some rh =>
      let t ← rh.handle params
      return t.map (sync := true) fun r => r.map ({response := ·, isComplete := true })

def routeLspRequest (method : String) (params : Json) : IO (Except RequestError DocumentUri) := do
  if ← isStatefulLspRequestMethod method then
    match ← lookupStatefulLspRequestHandler method with
    | none => return Except.error <| RequestError.methodNotFound method
    | some rh => return rh.fileSource params
  else
    match ← lookupLspRequestHandler method with
    | none => return Except.error <| RequestError.methodNotFound method
    | some rh => return rh.fileSource params

end HandlerTable
end Lean.Server
