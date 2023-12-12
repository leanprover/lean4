/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Init.System.IO
import Init.Data.ByteArray
import Lean.Data.RBMap

import Lean.Util.Paths

import Lean.Data.FuzzyMatching
import Lean.Data.Json
import Lean.Data.Lsp
import Lean.Server.Utils
import Lean.Server.Requests
import Lean.Server.References

/-!
For general server architecture, see `README.md`. This module implements the watchdog process.

## Watchdog state

Most LSP clients only send us file diffs, so to facilitate sending entire file contents to freshly restarted
workers, the watchdog needs to maintain the current state of each file. It can also use this state to detect changes
to the header and thus restart the corresponding worker, freeing its imports.

TODO(WN):
We may eventually want to keep track of approximately (since this isn't knowable exactly) where in the file a worker
crashed. Then on restart, we tell said worker to only parse up to that point and query the user about how to proceed
(continue OR allow the user to fix the bug and then continue OR ..). Without this, if the crash is deterministic,
users may be confused about why the server seemingly stopped working for a single file.

## Watchdog <-> worker communication

The watchdog process and its file worker processes communicate via LSP. If the necessity arises,
we might add non-standard commands similarly based on JSON-RPC. Most requests and notifications
are forwarded to the corresponding file worker process, with the exception of these notifications:

- textDocument/didOpen: Launch the file worker, create the associated watchdog state and launch a task to
                        asynchronously receive LSP packets from the worker (e.g. request responses).
- textDocument/didChange: Update the local file state so that it can be resent to restarted workers.
                          Then forward the `didChange` notification.
- textDocument/didClose: Signal a shutdown to the file worker and remove the associated watchdog state.

Moreover, we don't implement the full protocol at this level:

- Upon starting, the `initialize` request is forwarded to the worker, but it must not respond with its server
  capabilities. Consequently, the watchdog will not send an `initialized` notification to the worker.
- After `initialize`, the watchdog sends the corresponding `didOpen` notification with the full current state of
  the file. No additional `didOpen` notifications will be forwarded to the worker process.
- `$/cancelRequest` notifications are forwarded to all file workers.
- File workers are always terminated with an `exit` notification, without previously receiving a `shutdown` request.
  Similarly, they never receive a `didClose` notification.

## Watchdog <-> client communication

The watchdog itself should implement the LSP standard as closely as possible. However we reserve the right to add
non-standard extensions in case they're needed, for example to communicate tactic state.
-/

namespace Lean.Server.Watchdog

open IO
open Lsp
open JsonRpc
open System.Uri

section Utils
  def workerCfg : Process.StdioConfig := {
    stdin  := Process.Stdio.piped
    stdout := Process.Stdio.piped
    -- We pass workers' stderr through to the editor.
    stderr := Process.Stdio.inherit
  }

  /-- Events that worker-specific tasks signal to the main thread. -/
  inductive WorkerEvent where
    | terminated
    | importsChanged
    | crashed (e : IO.Error)
    | ioError (e : IO.Error)

  inductive WorkerState where
    /-- The watchdog can detect a crashed file worker in two places: When trying to send a message to the file worker
    and when reading a request reply.
    In the latter case, the forwarding task terminates and delegates a `crashed` event to the main task.
    Then, in both cases, the file worker has its state set to `crashed` and requests that are in-flight are errored.
    Upon receiving the next packet for that file worker, the file worker is restarted and the packet is forwarded
    to it. If the crash was detected while writing a packet, we queue that packet until the next packet for the file
    worker arrives. -/
    | crashed (queuedMsgs : Array JsonRpc.Message)
    | running

  abbrev PendingRequestMap := RBMap RequestID JsonRpc.Message compare
end Utils

section FileWorker
  structure FileWorker where
    doc                : DocumentMeta
    proc               : Process.Child workerCfg
    commTask           : Task WorkerEvent
    state              : WorkerState
    -- This should not be mutated outside of namespace FileWorker, as it is used as shared mutable state
    /-- The pending requests map contains all requests
    that have been received from the LSP client, but were not answered yet.
    We need them for forwarding cancellation requests to the correct worker as well as cleanly aborting
    requests on worker crashes. -/
    pendingRequestsRef : IO.Ref PendingRequestMap

  namespace FileWorker

  def stdin (fw : FileWorker) : FS.Stream :=
    FS.Stream.ofHandle fw.proc.stdin

  def stdout (fw : FileWorker) : FS.Stream :=
    FS.Stream.ofHandle fw.proc.stdout

  def erasePendingRequest (fw : FileWorker) (id : RequestID) : IO Unit :=
    fw.pendingRequestsRef.modify fun pendingRequests => pendingRequests.erase id

  def errorPendingRequests (fw : FileWorker) (hError : FS.Stream) (code : ErrorCode) (msg : String) : IO Unit := do
    let pendingRequests ← fw.pendingRequestsRef.modifyGet (fun pendingRequests => (pendingRequests, RBMap.empty))
    for ⟨id, _⟩ in pendingRequests do
      hError.writeLspResponseError { id := id, code := code, message := msg }

  end FileWorker
end FileWorker

section ServerM
  abbrev FileWorkerMap := RBMap DocumentUri FileWorker compare

  structure ServerContext where
    hIn            : FS.Stream
    hOut           : FS.Stream
    hLog           : FS.Stream
    /-- Command line arguments. -/
    args           : List String
    fileWorkersRef : IO.Ref FileWorkerMap
    /-- We store these to pass them to workers. -/
    initParams     : InitializeParams
    workerPath     : System.FilePath
    srcSearchPath  : System.SearchPath
    references     : IO.Ref References

  abbrev ServerM := ReaderT ServerContext IO

  def updateFileWorkers (val : FileWorker) : ServerM Unit := do
    (←read).fileWorkersRef.modify (fun fileWorkers => fileWorkers.insert val.doc.uri val)

  def findFileWorker? (uri : DocumentUri) : ServerM (Option FileWorker) :=
    return (← (←read).fileWorkersRef.get).find? uri

  def findFileWorker! (uri : DocumentUri) : ServerM FileWorker := do
    let some fw ← findFileWorker? uri
      | throwServerError s!"cannot find open document '{uri}'"
    return fw

  def eraseFileWorker (uri : DocumentUri) : ServerM Unit := do
    let s ← read
    s.fileWorkersRef.modify (fun fileWorkers => fileWorkers.erase uri)
    if let some path := fileUriToPath? uri then
      if let some module ← searchModuleNameOfFileName path s.srcSearchPath then
        s.references.modify fun refs => refs.removeWorkerRefs module

  def log (msg : String) : ServerM Unit := do
    let st ← read
    st.hLog.putStrLn msg
    st.hLog.flush

  def handleIleanInfoUpdate (fw : FileWorker) (params : LeanIleanInfoParams) : ServerM Unit := do
    let s ← read
    if let some path := fileUriToPath? fw.doc.uri then
      if let some module ← searchModuleNameOfFileName path s.srcSearchPath then
        s.references.modify fun refs => refs.updateWorkerRefs module params.version params.references

  def handleIleanInfoFinal (fw : FileWorker) (params : LeanIleanInfoParams) : ServerM Unit := do
    let s ← read
    if let some path := fileUriToPath? fw.doc.uri then
      if let some module ← searchModuleNameOfFileName path s.srcSearchPath then
        s.references.modify fun refs => refs.finalizeWorkerRefs module params.version params.references

  /-- Creates a Task which forwards a worker's messages into the output stream until an event
  which must be handled in the main watchdog thread (e.g. an I/O error) happens. -/
  private partial def forwardMessages (fw : FileWorker) : ServerM (Task WorkerEvent) := do
    let o := (←read).hOut
    let rec loop : ServerM WorkerEvent := do
      try
        let msg ← fw.stdout.readLspMessage
        -- Re. `o.writeLspMessage msg`:
        -- Writes to Lean I/O channels are atomic, so these won't trample on each other.
        match msg with
          | Message.response id _ => do
            fw.erasePendingRequest id
            o.writeLspMessage msg
          | Message.responseError id _ _ _ => do
            fw.erasePendingRequest id
            o.writeLspMessage msg
          | Message.notification "$/lean/ileanInfoUpdate" params =>
            if let some params := params then
              if let Except.ok params := FromJson.fromJson? <| ToJson.toJson params then
                handleIleanInfoUpdate fw params
          | Message.notification "$/lean/ileanInfoFinal" params =>
            if let some params := params then
              if let Except.ok params := FromJson.fromJson? <| ToJson.toJson params then
                handleIleanInfoFinal fw params
          | _ => o.writeLspMessage msg
      catch err =>
        -- If writeLspMessage from above errors we will block here, but the main task will
        -- quit eventually anyways if that happens
        let exitCode ← fw.proc.wait
        -- Remove surviving descendant processes, if any, such as from nested builds.
        -- On Windows, we instead rely on elan doing this.
        try fw.proc.kill catch _ => pure ()
        match exitCode with
        | 0 =>
          -- Worker was terminated
          fw.errorPendingRequests o ErrorCode.contentModified
            (s!"The file worker for {fw.doc.uri} has been terminated. Either the header has changed,"
            ++ " or the file was closed, or the server is shutting down.")
          -- one last message to clear the diagnostics for this file so that stale errors
          -- do not remain in the editor forever.
          publishDiagnostics fw.doc #[] o
          return WorkerEvent.terminated
        | 2 =>
          return .importsChanged
        | _ =>
          -- Worker crashed
          fw.errorPendingRequests o (if exitCode = 1 then ErrorCode.workerExited else ErrorCode.workerCrashed)
            s!"Server process for {fw.doc.uri} crashed, {if exitCode = 1 then "see stderr for exception" else "likely due to a stack overflow or a bug"}."
          publishProgressAtPos fw.doc 0 o (kind := LeanFileProgressKind.fatalError)
          return WorkerEvent.crashed err
      loop
    let task ← IO.asTask (loop $ ←read) Task.Priority.dedicated
    return task.map fun
      | Except.ok ev   => ev
      | Except.error e => WorkerEvent.ioError e

  def startFileWorker (m : DocumentMeta) : ServerM Unit := do
    publishProgressAtPos m 0 (← read).hOut
    let st ← read
    let workerProc ← Process.spawn {
      toStdioConfig := workerCfg
      cmd           := st.workerPath.toString
      args          := #["--worker"] ++ st.args.toArray ++ #[m.uri]
      -- open session for `kill` above
      setsid        := true
    }
    let pendingRequestsRef ← IO.mkRef (RBMap.empty : PendingRequestMap)
    let initialDependencyBuildMode := m.dependencyBuildMode
    let updatedDependencyBuildMode :=
      if initialDependencyBuildMode matches .once then
        -- By sending the first `didOpen` notification, we build the dependencies once
        -- => no future builds
        .never
      else
        initialDependencyBuildMode
    -- The task will never access itself, so this is fine
    let fw : FileWorker := {
      doc                := { m with dependencyBuildMode := updatedDependencyBuildMode}
      proc               := workerProc
      commTask           := Task.pure WorkerEvent.terminated
      state              := WorkerState.running
      pendingRequestsRef := pendingRequestsRef
    }
    let commTask ← forwardMessages fw
    let fw : FileWorker := { fw with commTask := commTask }
    fw.stdin.writeLspRequest ⟨0, "initialize", st.initParams⟩
    fw.stdin.writeLspNotification {
      method := "textDocument/didOpen"
      param  := {
        textDocument := {
          uri        := m.uri
          languageId := "lean"
          version    := m.version
          text       := m.text.source
        }
        dependencyBuildMode? := initialDependencyBuildMode
        : LeanDidOpenTextDocumentParams
      }
    }
    updateFileWorkers fw

  def terminateFileWorker (uri : DocumentUri) : ServerM Unit := do
    let fw ← findFileWorker! uri
    try
      fw.stdin.writeLspMessage (Message.notification "exit" none)
    catch _ =>
      /- The file worker must have crashed just when we were about to terminate it!
        That's fine - just forget about it then.
        (on didClose we won't need the crashed file worker anymore,
        when the header changed we'll start a new one right after
        anyways and when we're shutting down the server
        it's over either way.) -/
      return
    eraseFileWorker uri

  def handleCrash (uri : DocumentUri) (queuedMsgs : Array JsonRpc.Message) : ServerM Unit := do
    updateFileWorkers { ←findFileWorker! uri with state := WorkerState.crashed queuedMsgs }

  /-- Tries to write a message, sets the state of the FileWorker to `crashed` if it does not succeed
      and restarts the file worker if the `crashed` flag was already set. Just logs an error if there
      is no FileWorker at this `uri`.
      Messages that couldn't be sent can be queued up via the queueFailedMessage flag and
      will be discharged after the FileWorker is restarted. -/
  def tryWriteMessage (uri : DocumentUri) (msg : JsonRpc.Message) (queueFailedMessage := true) (restartCrashedWorker := false) :
      ServerM Unit := do
    let some fw ← findFileWorker? uri
      | do
        (←read).hLog.putStrLn s!"Cannot send message to unknown document '{uri}':\n{(toJson msg).compress}"
        return
    match fw.state with
    | WorkerState.crashed queuedMsgs =>
      let mut queuedMsgs := queuedMsgs
      if queueFailedMessage then
        queuedMsgs := queuedMsgs.push msg
      if !restartCrashedWorker then
        return
      -- restart the crashed FileWorker
      eraseFileWorker uri
      startFileWorker fw.doc
      let newFw ← findFileWorker! uri
      let mut crashedMsgs := #[]
      -- try to discharge all queued msgs, tracking the ones that we can't discharge
      for msg in queuedMsgs do
        try
          newFw.stdin.writeLspMessage msg
        catch _ =>
          crashedMsgs := crashedMsgs.push msg
      if ¬ crashedMsgs.isEmpty then
        handleCrash uri crashedMsgs
    | WorkerState.running =>
      let initialQueuedMsgs :=
        if queueFailedMessage then
          #[msg]
        else
          #[]
      try
        fw.stdin.writeLspMessage msg
      catch _ =>
        handleCrash uri initialQueuedMsgs
end ServerM

section RequestHandling

open FuzzyMatching

def findDefinitions (p : TextDocumentPositionParams) : ServerM <| Array Location := do
  let mut definitions := #[]
  if let some path := fileUriToPath? p.textDocument.uri then
    let srcSearchPath := (← read).srcSearchPath
    if let some module ← searchModuleNameOfFileName path srcSearchPath then
      let references ← (← read).references.get
      for ident in references.findAt module p.position (includeStop := true) do
        if let some definition ← references.definitionOf? ident srcSearchPath then
          definitions := definitions.push definition
  return definitions

def handleReference (p : ReferenceParams) : ServerM (Array Location) := do
  let mut result := #[]
  if let some path := fileUriToPath? p.textDocument.uri then
    let srcSearchPath := (← read).srcSearchPath
    if let some module ← searchModuleNameOfFileName path srcSearchPath then
      let references ← (← read).references.get
      for ident in references.findAt module p.position (includeStop := true) do
        let identRefs ← references.referringTo module ident srcSearchPath p.context.includeDeclaration
        result := result.append identRefs
  return result

def handleWorkspaceSymbol (p : WorkspaceSymbolParams) : ServerM (Array SymbolInformation) := do
  if p.query.isEmpty then
    return #[]
  let references ← (← read).references.get
  let srcSearchPath := (← read).srcSearchPath
  let symbols ← references.definitionsMatching srcSearchPath (maxAmount? := none)
    fun name =>
      let name := privateToUserName? name |>.getD name
      if let some score := fuzzyMatchScoreWithThreshold? p.query name.toString then
        some (name.toString, score)
      else
        none
  return symbols
    |>.qsort (fun ((_, s1), _) ((_, s2), _) => s1 > s2)
    |>.extract 0 100 -- max amount
    |>.map fun ((name, _), location) =>
      { name, kind := SymbolKind.constant, location }

def handlePrepareRename (p : PrepareRenameParams) : ServerM (Option Range) := do
  -- This just checks that the cursor is over a renameable identifier
  if let some path := System.Uri.fileUriToPath? p.textDocument.uri then
    let srcSearchPath := (← read).srcSearchPath
    if let some module ← searchModuleNameOfFileName path srcSearchPath then
      let references ← (← read).references.get
      return references.findRange? module p.position (includeStop := true)
  return none

def handleRename (p : RenameParams) : ServerM Lsp.WorkspaceEdit := do
  if (String.toName p.newName).isAnonymous then
    throwServerError s!"Can't rename: `{p.newName}` is not an identifier"
  let mut refs : HashMap DocumentUri (RBMap Lsp.Position Lsp.Position compare) := ∅
  for { uri, range } in (← handleReference { p with context.includeDeclaration := true }) do
    refs := refs.insert uri <| (refs.findD uri ∅).insert range.start range.end
  -- We have to filter the list of changes to put the ranges in order and
  -- remove any duplicates or overlapping ranges, or else the rename will not apply
  let changes := refs.fold (init := ∅) fun changes uri map => Id.run do
    let mut last := ⟨0, 0⟩
    let mut arr := #[]
    for (start, stop) in map do
      if last ≤ start then
        arr := arr.push { range := ⟨start, stop⟩, newText := p.newName }
        last := stop
    return changes.insert uri arr
  return { changes? := some changes }

end RequestHandling

section NotificationHandling
  def handleDidOpen (p : LeanDidOpenTextDocumentParams) : ServerM Unit :=
    let doc := p.textDocument
    /- NOTE(WN): `toFileMap` marks line beginnings as immediately following
       "\n", which should be enough to handle both LF and CRLF correctly.
       This is because LSP always refers to characters by (line, column),
       so if we get the line number correct it shouldn't matter that there
       is a CR there. -/
    startFileWorker ⟨doc.uri, doc.version, doc.text.toFileMap, p.dependencyBuildMode?.getD .always⟩

  def handleDidChange (p : DidChangeTextDocumentParams) : ServerM Unit := do
    let doc := p.textDocument
    let changes := p.contentChanges
    let fw ← findFileWorker! p.textDocument.uri
    let oldDoc := fw.doc
    let newVersion := doc.version?.getD 0
    if changes.isEmpty then
      return
    let newDocText := foldDocumentChanges changes oldDoc.text
    let newDoc : DocumentMeta := ⟨doc.uri, newVersion, newDocText, oldDoc.dependencyBuildMode⟩
    updateFileWorkers { fw with doc := newDoc }
    tryWriteMessage doc.uri (Notification.mk "textDocument/didChange" p) (restartCrashedWorker := true)

  def handleDidClose (p : DidCloseTextDocumentParams) : ServerM Unit :=
    terminateFileWorker p.textDocument.uri

  def handleDidChangeWatchedFiles (p : DidChangeWatchedFilesParams) : ServerM Unit := do
    let references := (← read).references
    let oleanSearchPath ← Lean.searchPathRef.get
    let ileans ← oleanSearchPath.findAllWithExt "ilean"
    for change in p.changes do
      if let some path := fileUriToPath? change.uri then
      if let FileChangeType.Deleted := change.type then
        references.modify (fun r => r.removeIlean path)
      else if ileans.contains path then
        try
          let ilean ← Ilean.load path
          if let FileChangeType.Changed := change.type then
            references.modify (fun r => r.removeIlean path |>.addIlean path ilean)
          else
            references.modify (fun r => r.addIlean path ilean)
        catch
          -- ilean vanished, ignore error
          | .noFileOrDirectory .. => references.modify (·.removeIlean path)
          | e => throw e

  def handleCancelRequest (p : CancelParams) : ServerM Unit := do
    let fileWorkers ← (←read).fileWorkersRef.get
    for ⟨uri, fw⟩ in fileWorkers do
      -- Cancelled requests still require a response, so they can't be removed
      -- from the pending requests map.
      if (← fw.pendingRequestsRef.get).contains p.id then
        tryWriteMessage uri (Notification.mk "$/cancelRequest" p) (queueFailedMessage := false)

  def forwardNotification {α : Type} [ToJson α] [FileSource α] (method : String) (params : α) : ServerM Unit :=
    tryWriteMessage (fileSource params) (Notification.mk method params) (queueFailedMessage := true)
end NotificationHandling

section MessageHandling
  def parseParams (paramType : Type) [FromJson paramType] (params : Json) : ServerM paramType :=
    match fromJson? params with
    | Except.ok parsed => pure parsed
    | Except.error inner => throwServerError s!"Got param with wrong structure: {params.compress}\n{inner}"

  def forwardRequestToWorker (id : RequestID) (method : String) (params : Json) : ServerM Unit := do
    let uri: DocumentUri ←
      -- This request is handled specially.
      if method == "$/lean/rpc/connect" then
        let ps ← parseParams Lsp.RpcConnectParams params
        pure <| fileSource ps
      else match (← routeLspRequest method params) with
      | Except.error e =>
        (←read).hOut.writeLspResponseError <| e.toLspResponseError id
        return
      | Except.ok uri => pure uri
    let some fw ← findFileWorker? uri
      /- Clients may send requests to closed files, which we respond to with an error.
      For example, VSCode sometimes sends requests just after closing a file,
      and RPC clients may also do so, e.g. due to remaining timers. -/
      | do
        (←read).hOut.writeLspResponseError
          { id      := id
            /- Some clients (VSCode) also send requests *before* opening a file. We reply
            with `contentModified` as that does not display a "request failed" popup. -/
            code    := ErrorCode.contentModified
            message := s!"Cannot process request to closed file '{uri}'" }
        return
    let r := Request.mk id method params
    fw.pendingRequestsRef.modify (·.insert id r)
    tryWriteMessage uri r

  def handleRequest (id : RequestID) (method : String) (params : Json) : ServerM Unit := do
    let handle α β [FromJson α] [ToJson β] (handler : α → ServerM β) : ServerM Unit := do
      let hOut := (← read).hOut
      try
        let params ← parseParams α params
        let result ← handler params
        hOut.writeLspResponse ⟨id, result⟩
      catch
        -- TODO Do fancier error handling, like in file worker?
        | e => hOut.writeLspResponseError {
          id := id
          code := ErrorCode.internalError
          message := s!"Failed to process request {id}: {e}"
        }
    -- If a definition is in a different, modified file, the ilean data should
    -- have the correct location while the olean still has outdated info from
    -- the last compilation. This is easier than catching the client's reply and
    -- fixing the definition's location afterwards, but it doesn't work for
    -- go-to-type-definition.
    if method == "textDocument/definition" || method == "textDocument/declaration" then
      let params ← parseParams TextDocumentPositionParams params
      let definitions ← findDefinitions params
      if !definitions.isEmpty then
        (← read).hOut.writeLspResponse ⟨id, definitions⟩
        return
    match method with
      | "textDocument/references" => handle ReferenceParams (Array Location) handleReference
      | "workspace/symbol" => handle WorkspaceSymbolParams (Array SymbolInformation) handleWorkspaceSymbol
      | "textDocument/prepareRename" => handle PrepareRenameParams (Option Range) handlePrepareRename
      | "textDocument/rename" => handle RenameParams WorkspaceEdit handleRename
      | _ => forwardRequestToWorker id method params

  def handleNotification (method : String) (params : Json) : ServerM Unit := do
    let handle := (fun α [FromJson α] (handler : α → ServerM Unit) => parseParams α params >>= handler)
    match method with
    | "textDocument/didOpen"            => handle _ handleDidOpen
    | "textDocument/didChange"          => handle DidChangeTextDocumentParams handleDidChange
    | "textDocument/didClose"           => handle DidCloseTextDocumentParams handleDidClose
    | "workspace/didChangeWatchedFiles" => handle DidChangeWatchedFilesParams handleDidChangeWatchedFiles
    | "$/cancelRequest"                 => handle CancelParams handleCancelRequest
    | "$/lean/rpc/connect"              => handle RpcConnectParams (forwardNotification method)
    | "$/lean/rpc/release"              => handle RpcReleaseParams (forwardNotification method)
    | "$/lean/rpc/keepAlive"            => handle RpcKeepAliveParams (forwardNotification method)
    | _                                 =>
      if !"$/".isPrefixOf method then  -- implementation-dependent notifications can be safely ignored
        (←read).hLog.putStrLn s!"Got unsupported notification: {method}"
end MessageHandling

section MainLoop
  def shutdown : ServerM Unit := do
    let fileWorkers ← (←read).fileWorkersRef.get
    for ⟨uri, _⟩ in fileWorkers do
      terminateFileWorker uri
    for ⟨_, fw⟩ in fileWorkers do
      discard <| IO.wait fw.commTask

  inductive ServerEvent where
    | workerEvent (fw : FileWorker) (ev : WorkerEvent)
    | clientMsg (msg : JsonRpc.Message)
    | clientError (e : IO.Error)

  def runClientTask : ServerM (Task ServerEvent) := do
    let st ← read
    let readMsgAction : IO ServerEvent := do
      /- Runs asynchronously. -/
      let msg ← st.hIn.readLspMessage
      pure <| ServerEvent.clientMsg msg
    let clientTask := (← IO.asTask readMsgAction).map fun
      | Except.ok ev   => ev
      | Except.error e => ServerEvent.clientError e
    return clientTask

  partial def mainLoop (clientTask : Task ServerEvent) : ServerM Unit := do
    let st ← read
    let workers ← st.fileWorkersRef.get
    let mut workerTasks := #[]
    for (_, fw) in workers do
      if let WorkerState.running := fw.state then
        workerTasks := workerTasks.push <| fw.commTask.map (ServerEvent.workerEvent fw)

    let ev ← IO.waitAny (clientTask :: workerTasks.toList)
    match ev with
    | ServerEvent.clientMsg msg =>
      match msg with
      | Message.request id "shutdown" _ =>
        shutdown
        st.hOut.writeLspResponse ⟨id, Json.null⟩
      | Message.request id method (some params) =>
        handleRequest id method (toJson params)
        mainLoop (←runClientTask)
      | Message.response .. =>
        -- TODO: handle client responses
        mainLoop (←runClientTask)
      | Message.responseError _ _ e .. =>
        throwServerError s!"Unhandled response error: {e}"
      | Message.notification method (some params) =>
        handleNotification method (toJson params)
        mainLoop (←runClientTask)
      | _ => throwServerError "Got invalid JSON-RPC message"
    | ServerEvent.clientError e => throw e
    | ServerEvent.workerEvent fw ev =>
      match ev with
      | WorkerEvent.ioError e =>
        throwServerError s!"IO error while processing events for {fw.doc.uri}: {e}"
      | WorkerEvent.crashed _ =>
        handleCrash fw.doc.uri #[]
        mainLoop clientTask
      | WorkerEvent.terminated =>
        throwServerError "Internal server error: got termination event for worker that should have been removed"
      | .importsChanged =>
        startFileWorker fw.doc
        mainLoop clientTask
end MainLoop

def mkLeanServerCapabilities : ServerCapabilities := {
  textDocumentSync? := some {
    openClose         := true
    change            := TextDocumentSyncKind.incremental
    willSave          := false
    willSaveWaitUntil := false
    save?             := none
  }
  -- refine
  completionProvider? := some {
    triggerCharacters? := some #["."]
  }
  hoverProvider := true
  declarationProvider := true
  definitionProvider := true
  typeDefinitionProvider := true
  referencesProvider := true
  renameProvider? := some {
    prepareProvider := true
  }
  workspaceSymbolProvider := true
  documentHighlightProvider := true
  documentSymbolProvider := true
  foldingRangeProvider := true
  semanticTokensProvider? := some {
    legend := {
      tokenTypes     := SemanticTokenType.names
      tokenModifiers := SemanticTokenModifier.names
    }
    full  := true
    range := true
  }
  codeActionProvider? := some {
    resolveProvider? := true,
    codeActionKinds? := some #["quickfix", "refactor"]
  }
}

def initAndRunWatchdogAux : ServerM Unit := do
  let st ← read
  try
    discard $ st.hIn.readLspNotificationAs "initialized" InitializedParams
    let clientTask ← runClientTask
    mainLoop clientTask
  catch err =>
    shutdown
    throw err
  /- NOTE(WN): It looks like instead of sending the `exit` notification,
  VSCode just closes the stream. In that case, pretend we got an `exit`. -/
  let Message.notification "exit" none ←
    try st.hIn.readLspMessage
    catch _ => pure (Message.notification "exit" none)
    | throwServerError "Got `shutdown` request, expected an `exit` notification"

def findWorkerPath : IO System.FilePath := do
  let mut workerPath ← IO.appPath
  if let some path := (←IO.getEnv "LEAN_SYSROOT") then
    workerPath := System.FilePath.mk path / "bin" / "lean" |>.withExtension System.FilePath.exeExtension
  if let some path := (←IO.getEnv "LEAN_WORKER_PATH") then
    workerPath := System.FilePath.mk path
  return workerPath

def loadReferences : IO References := do
  let oleanSearchPath ← Lean.searchPathRef.get
  let mut refs := References.empty
  for path in ← oleanSearchPath.findAllWithExt "ilean" do
    try
      refs := refs.addIlean path (← Ilean.load path)
    catch _ =>
      -- could be a race with the build system, for example
      -- ilean load errors should not be fatal, but we *should* log them
      -- when we add logging to the server
      pure ()
  return refs

def initAndRunWatchdog (args : List String) (i o e : FS.Stream) : IO Unit := do
  let workerPath ← findWorkerPath
  let srcSearchPath ← initSrcSearchPath
  let references ← IO.mkRef (← loadReferences)
  let fileWorkersRef ← IO.mkRef (RBMap.empty : FileWorkerMap)
  let i ← maybeTee "wdIn.txt" false i
  let o ← maybeTee "wdOut.txt" true o
  let e ← maybeTee "wdErr.txt" true e
  let initRequest ← i.readLspRequestAs "initialize" InitializeParams
  o.writeLspResponse {
    id     := initRequest.id
    result := {
      capabilities := mkLeanServerCapabilities
      serverInfo?  := some {
        name     := "Lean 4 Server"
        version? := "0.1.2"
      }
      : InitializeResult
    }
  }
  o.writeLspRequest {
    id := RequestID.str "register_ilean_watcher"
    method := "client/registerCapability"
    param := some {
      registrations := #[ {
        id := "ilean_watcher"
        method := "workspace/didChangeWatchedFiles"
        registerOptions := some <| toJson {
          watchers := #[ { globPattern := "**/*.ilean" } ]
        : DidChangeWatchedFilesRegistrationOptions }
      } ]
    : RegistrationParams }
  }
  ReaderT.run initAndRunWatchdogAux {
    hIn            := i
    hOut           := o
    hLog           := e
    args           := args
    fileWorkersRef := fileWorkersRef
    initParams     := initRequest.param
    workerPath
    srcSearchPath
    references
    : ServerContext
  }

@[export lean_server_watchdog_main]
def watchdogMain (args : List String) : IO UInt32 := do
  let i ← IO.getStdin
  let o ← IO.getStdout
  let e ← IO.getStderr
  try
    initAndRunWatchdog args i o e
    return 0
  catch err =>
    e.putStrLn s!"Watchdog error: {err}"
    return 1

end Lean.Server.Watchdog
