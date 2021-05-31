/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Init.System.IO
import Init.Data.ByteArray
import Std.Data.RBMap

import Lean.Elab.Import

import Lean.Data.Lsp
import Lean.Server.FileSource
import Lean.Server.Utils

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
- textDocument/didChange: Update the local file state. If the header was mutated,
                          signal a shutdown to the file worker by closing the I/O channels.
                          Then restart the file worker. Otherwise, forward the `didChange` notification.
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
open Std (RBMap RBMap.empty)
open Lsp
open JsonRpc

section Utils
  structure OpenDocument where
    meta      : DocumentMeta
    headerAst : Syntax

  def workerCfg : Process.StdioConfig := {
    stdin  := Process.Stdio.piped
    stdout := Process.Stdio.piped
    -- We pass workers' stderr through to the editor.
    stderr := Process.Stdio.inherit
  }

  /-- Events that worker-specific tasks signal to the main thread. -/
  inductive WorkerEvent where
    /- A synthetic event signalling that the grouped edits should be processed. -/
    | processGroupedEdits
    | terminated
    | crashed (e : IO.Error)
    | ioError (e : IO.Error)

  inductive WorkerState where
    /- The watchdog can detect a crashed file worker in two places: When trying to send a message to the file worker
       and when reading a request reply.
       In the latter case, the forwarding task terminates and delegates a `crashed` event to the main task.
       Then, in both cases, the file worker has its state set to `crashed` and requests that are in-flight are errored.
       Upon receiving the next packet for that file worker, the file worker is restarted and the packet is forwarded
       to it. If the crash was detected while writing a packet, we queue that packet until the next packet for the file
       worker arrives. -/
    | crashed (queuedMsgs : Array JsonRpc.Message)
    | running

  abbrev PendingRequestMap := RBMap RequestID JsonRpc.Message compare

  private def parseHeaderAst (input : String) : IO Syntax := do
    let inputCtx   := Parser.mkInputContext input "<input>"
    let (stx, _, _) ← Parser.parseHeader inputCtx
    return stx
end Utils

section FileWorker
  /-- A group of edits which will be processed at a future instant. -/
  structure GroupedEdits where
    /-- When to process the edits. -/
    applyTime  : Nat
    params     : DidChangeTextDocumentParams
    /-- Signals when `applyTime` has been reached. -/
    signalTask : Task WorkerEvent
    /-- We should not reorder messages when delaying edits, so we queue other messages since the last request here. -/
    queuedMsgs : Array JsonRpc.Message

  structure FileWorker where
    doc                : OpenDocument
    proc               : Process.Child workerCfg
    commTask           : Task WorkerEvent
    state              : WorkerState
    -- This should not be mutated outside of namespace FileWorker, as it is used as shared mutable state
    pendingRequestsRef : IO.Ref PendingRequestMap
    groupedEditsRef    : IO.Ref (Option GroupedEdits)

  namespace FileWorker

  def stdin (fw : FileWorker) : FS.Stream :=
    FS.Stream.ofHandle fw.proc.stdin

  def stdout (fw : FileWorker) : FS.Stream :=
    FS.Stream.ofHandle fw.proc.stdout

  def readMessage (fw : FileWorker) : IO JsonRpc.Message := do
    let msg ← fw.stdout.readLspMessage
    if let Message.response id _ := msg then
      fw.pendingRequestsRef.modify (fun pendingRequests => pendingRequests.erase id)
    if let Message.responseError id _ _ _ := msg then
      fw.pendingRequestsRef.modify (fun pendingRequests => pendingRequests.erase id)
    return msg

  def errorPendingRequests (fw : FileWorker) (hError : FS.Stream) (code : ErrorCode) (msg : String) : IO Unit := do
    let pendingRequests ← fw.pendingRequestsRef.modifyGet (fun pendingRequests => (pendingRequests, RBMap.empty))
    for ⟨id, _⟩ in pendingRequests do
      hError.writeLspResponseError { id := id, code := code, message := msg }

  partial def runEditsSignalTask (fw : FileWorker) : IO (Task WorkerEvent) := do
    -- check `applyTime` in a loop since it might have been postponed by a subsequent edit notification
    let rec loopAction : IO WorkerEvent := do
      let now ← monoMsNow
      let some ge ← fw.groupedEditsRef.get
        | throwServerError "Internal error: empty grouped edits reference in signal task"
      if ge.applyTime ≤ now then
        return WorkerEvent.processGroupedEdits
      else
        IO.sleep <| UInt32.ofNat <| ge.applyTime - now
        loopAction

    let t ← IO.asTask loopAction
    return t.map fun
      | Except.ok ev   => ev
      | Except.error e => WorkerEvent.ioError e

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
    editDelay      : Nat
    workerPath     : System.FilePath

  abbrev ServerM := ReaderT ServerContext IO

  def updateFileWorkers (val : FileWorker) : ServerM Unit := do
    (←read).fileWorkersRef.modify (fun fileWorkers => fileWorkers.insert val.doc.meta.uri val)

  def findFileWorker (uri : DocumentUri) : ServerM FileWorker := do
    match (←(←read).fileWorkersRef.get).find? uri with
    | some fw => fw
    | none    => throwServerError s!"Got unknown document URI ({uri})"

  def eraseFileWorker (uri : DocumentUri) : ServerM Unit := do
    (←read).fileWorkersRef.modify (fun fileWorkers => fileWorkers.erase uri)

  def log (msg : String) : ServerM Unit := do
    let st ← read
    st.hLog.putStrLn msg
    st.hLog.flush

  /-- Creates a Task which forwards a worker's messages into the output stream until an event
  which must be handled in the main watchdog thread (e.g. an I/O error) happens. -/
  private partial def forwardMessages (fw : FileWorker) : ServerM (Task WorkerEvent) := do
    let o := (←read).hOut
    let rec loop : ServerM WorkerEvent := do
      try
        let msg ← fw.readMessage
        -- Writes to Lean I/O channels are atomic, so these won't trample on each other.
        o.writeLspMessage msg
      catch err =>
        -- If writeLspMessage from above errors we will block here, but the main task will
        -- quit eventually anyways if that happens
        let exitCode ← fw.proc.wait
        if exitCode = 0 then
          -- Worker was terminated
          fw.errorPendingRequests o ErrorCode.contentModified
            ("The file worker has been terminated. Either the header has changed,"
            ++ " or the file was closed, or the server is shutting down.")
          return WorkerEvent.terminated
        else
          -- Worker crashed
          fw.errorPendingRequests o ErrorCode.internalError
            s!"Server process for {fw.doc.meta.uri} crashed, {if exitCode = 1 then "see stderr for exception" else "likely due to a stack overflow in user code"}."
          return WorkerEvent.crashed err
      loop
    let task ← IO.asTask (loop $ ←read) Task.Priority.dedicated
    task.map $ fun
      | Except.ok ev   => ev
      | Except.error e => WorkerEvent.ioError e

  def startFileWorker (m : DocumentMeta) : ServerM Unit := do
    publishDiagnostics m #[{ range := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, severity? := DiagnosticSeverity.information, message := "starting new server for file..." }] (← read).hOut
    let st ← read
    let headerAst ← parseHeaderAst m.text.source
    let workerProc ← Process.spawn {
      toStdioConfig := workerCfg
      cmd           := st.workerPath.toString
      args          := #["--worker"] ++ st.args.toArray
    }
    let pendingRequestsRef ← IO.mkRef (RBMap.empty : PendingRequestMap)
    -- The task will never access itself, so this is fine
    let fw : FileWorker := {
      doc                := ⟨m, headerAst⟩
      proc               := workerProc
      commTask           := Task.pure WorkerEvent.terminated
      state              := WorkerState.running
      pendingRequestsRef := pendingRequestsRef
      groupedEditsRef    := ← IO.mkRef none
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
        } : DidOpenTextDocumentParams
      }
    }
    updateFileWorkers fw

  def terminateFileWorker (uri : DocumentUri) : ServerM Unit := do
    /- The file worker must have crashed just when we were about to terminate it!
       That's fine - just forget about it then.
       (on didClose we won't need the crashed file worker anymore,
       when the header changed we'll start a new one right after
       anyways and when we're shutting down the server
       it's over either way.) -/
    try (←findFileWorker uri).stdin.writeLspMessage (Message.notification "exit" none)
    catch err => ()
    eraseFileWorker uri

  def handleCrash (uri : DocumentUri) (queuedMsgs : Array JsonRpc.Message) : ServerM Unit := do
    updateFileWorkers { ←findFileWorker uri with state := WorkerState.crashed queuedMsgs }

  /-- Tries to write a message, sets the state of the FileWorker to `crashed` if it does not succeed
      and restarts the file worker if the `crashed` flag was already set.
      Messages that couldn't be sent can be queued up via the queueFailedMessage flag and
      will be discharged after the FileWorker is restarted. -/
  def tryWriteMessage (uri : DocumentUri) (msg : JsonRpc.Message) (queueFailedMessage := true) (restartCrashedWorker := false) :
      ServerM Unit := do
    let fw ← findFileWorker uri
    let pendingEdit ← fw.groupedEditsRef.modifyGet fun
      | some ge => (true, some { ge with queuedMsgs := ge.queuedMsgs.push msg })
      | none    => (false, none)
    if pendingEdit then
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
      startFileWorker fw.doc.meta
      let newFw ← findFileWorker uri
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

section NotificationHandling
  def handleDidOpen (p : DidOpenTextDocumentParams) : ServerM Unit :=
    let doc := p.textDocument
    /- NOTE(WN): `toFileMap` marks line beginnings as immediately following
       "\n", which should be enough to handle both LF and CRLF correctly.
       This is because LSP always refers to characters by (line, column),
       so if we get the line number correct it shouldn't matter that there
       is a CR there. -/
    startFileWorker ⟨doc.uri, doc.version, doc.text.toFileMap⟩

  def handleEdits (fw : FileWorker) : ServerM Unit := do
    let some ge ← fw.groupedEditsRef.modifyGet (·, none)
      | throwServerError "Internal error: empty grouped edits reference"
    let doc := ge.params.textDocument
    let changes := ge.params.contentChanges
    let oldDoc := fw.doc
    let some newVersion ← pure doc.version?
      | throwServerError "Expected version number"
    if newVersion <= oldDoc.meta.version then
      throwServerError "Got outdated version number"
    if changes.isEmpty then
      return
    let (newDocText, _) := foldDocumentChanges changes oldDoc.meta.text
    let newMeta : DocumentMeta := ⟨doc.uri, newVersion, newDocText⟩
    let newHeaderAst ← parseHeaderAst newDocText.source
    if newHeaderAst != oldDoc.headerAst then
      terminateFileWorker doc.uri
      startFileWorker newMeta
    else
      let newDoc : OpenDocument := ⟨newMeta, oldDoc.headerAst⟩
      updateFileWorkers { fw with doc := newDoc }
      tryWriteMessage doc.uri (Notification.mk "textDocument/didChange" ge.params) (restartCrashedWorker := true)
      for msg in ge.queuedMsgs do
        tryWriteMessage doc.uri msg

  def handleDidClose (p : DidCloseTextDocumentParams) : ServerM Unit :=
    terminateFileWorker p.textDocument.uri

  def handleCancelRequest (p : CancelParams) : ServerM Unit := do
    let fileWorkers ← (←read).fileWorkersRef.get
    for ⟨uri, fw⟩ in fileWorkers do
      let req? ← fw.pendingRequestsRef.modifyGet (fun pendingRequests =>
        (pendingRequests.find? p.id, pendingRequests.erase p.id))
      if let some req := req? then
        tryWriteMessage uri (Notification.mk "$/cancelRequest" p) (queueFailedMessage := false)
end NotificationHandling

section MessageHandling
  def parseParams (paramType : Type) [FromJson paramType] (params : Json) : ServerM paramType :=
      match fromJson? params with
      | some parsed => pure parsed
      | none        => throwServerError s!"Got param with wrong structure: {params.compress}"

  def handleRequest (id : RequestID) (method : String) (params : Json) : ServerM Unit := do
    let handle := fun α [FromJson α] [ToJson α] [FileSource α] => do
      let parsedParams ← parseParams α params
      let uri := fileSource parsedParams
      let fw ← try
        findFileWorker uri
      catch _ =>
        -- VS Code sometimes sends us requests just after closing a file?
        -- This is permitted by the spec, but seems pointless, and there's not much we can do,
        -- so we return an error instead.
        (←read).hOut.writeLspResponseError
          { id      := id
            code    := ErrorCode.contentModified
            message := s!"Cannot process request to closed file '{uri}'" }
        return
      let r := Request.mk id method params
      fw.pendingRequestsRef.modify (·.insert id r)
      tryWriteMessage uri r
    match method with
    | "textDocument/waitForDiagnostics"   => handle WaitForDiagnosticsParams
    | "textDocument/completion"           => handle CompletionParams
    | "textDocument/hover"                => handle HoverParams
    | "textDocument/declaration"          => handle DeclarationParams
    | "textDocument/definition"           => handle DefinitionParams
    | "textDocument/typeDefinition"       => handle TypeDefinitionParams
    | "textDocument/documentHighlight"    => handle DocumentHighlightParams
    | "textDocument/documentSymbol"       => handle DocumentSymbolParams
    | "textDocument/semanticTokens/range" => handle SemanticTokensRangeParams
    | "textDocument/semanticTokens/full"  => handle SemanticTokensParams
    | "$/lean/plainGoal"                  => handle PlainGoalParams
    | "$/lean/plainTermGoal"              => handle PlainTermGoalParams
    | _                                   =>
      (←read).hOut.writeLspResponseError
        { id      := id
          code    := ErrorCode.methodNotFound
          message := s!"Unsupported request method: {method}" }

  def handleNotification (method : String) (params : Json) : ServerM Unit := do
    let handle := (fun α [FromJson α] (handler : α → ServerM Unit) => parseParams α params >>= handler)
    match method with
    | "textDocument/didOpen"   => handle DidOpenTextDocumentParams handleDidOpen
    /- NOTE: textDocument/didChange is handled in the main loop. -/
    | "textDocument/didClose"  => handle DidCloseTextDocumentParams handleDidClose
    | "$/cancelRequest"        => handle CancelParams handleCancelRequest
    | _                        =>
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
      ServerEvent.clientMsg msg
    let clientTask := (←IO.asTask readMsgAction).map $ fun
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
        if let some ge ← fw.groupedEditsRef.get then
          workerTasks := workerTasks.push <| ge.signalTask.map (ServerEvent.workerEvent fw)

    let ev ← IO.waitAny (workerTasks.push clientTask |>.toList)
    match ev with
    | ServerEvent.clientMsg msg =>
      match msg with
      | Message.request id "shutdown" _ =>
        shutdown
        st.hOut.writeLspResponse ⟨id, Json.null⟩
      | Message.request id method (some params) =>
        handleRequest id method (toJson params)
        mainLoop (←runClientTask)
      | Message.notification "textDocument/didChange" (some params) =>
        let p ← parseParams DidChangeTextDocumentParams (toJson params)
        let fw ← findFileWorker p.textDocument.uri
        let now ← monoMsNow
        /- We wait `editDelay`ms since last edit before applying the changes. -/
        let applyTime := now + st.editDelay
        let pendingEdit ← fw.groupedEditsRef.modifyGet fun
          | some ge => (some ge.queuedMsgs, some { ge with
            applyTime := applyTime
            params.textDocument := p.textDocument
            params.contentChanges := ge.params.contentChanges ++ p.contentChanges
            -- drain now-outdated messages and respond with `contentModified` below
            queuedMsgs := #[] })
          | none    => (none, some {
            applyTime := applyTime
            params := p
            /- This is overwritten just below. -/
            signalTask := Task.pure WorkerEvent.processGroupedEdits
            queuedMsgs := #[] })
        match pendingEdit with
        | some queuedMsgs =>
          for msg in queuedMsgs do
            match msg with
            | JsonRpc.Message.request id _ _ =>
              (← read).hOut.writeLspResponseError {
                id := id
                code := ErrorCode.contentModified
                message := "File changed."
              }
            | _ => () -- notifications do not need to be cancelled
        | _ =>
          let t ← fw.runEditsSignalTask
          fw.groupedEditsRef.modify (Option.map fun ge => { ge with signalTask := t } )
        mainLoop (←runClientTask)
      | Message.notification method (some params) =>
        handleNotification method (toJson params)
        mainLoop (←runClientTask)
      | _ => throwServerError "Got invalid JSON-RPC message"
    | ServerEvent.clientError e => throw e
    | ServerEvent.workerEvent fw ev =>
      match ev with
      | WorkerEvent.processGroupedEdits =>
        handleEdits fw
        mainLoop clientTask
      | WorkerEvent.ioError e =>
        throwServerError s!"IO error while processing events for {fw.doc.meta.uri}: {e}"
      | WorkerEvent.crashed e =>
        handleCrash fw.doc.meta.uri #[]
        mainLoop clientTask
      | WorkerEvent.terminated =>
        throwServerError "Internal server error: got termination event for worker that should have been removed"
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
  documentHighlightProvider := true
  documentSymbolProvider := true
  semanticTokensProvider? := some {
    legend := {
      tokenTypes     := SemanticTokenType.names
      tokenModifiers := #[]
    }
    full  := true
    range := true
  }
}

def initAndRunWatchdogAux : ServerM Unit := do
  let st ← read
  try
    discard $ st.hIn.readLspNotificationAs "initialized" InitializedParams
    let clientTask ← runClientTask
    mainLoop clientTask
    let Message.notification "exit" none ← st.hIn.readLspMessage
      | throwServerError "Expected an exit notification"
  catch err =>
    shutdown
    throw err

def initAndRunWatchdog (args : List String) (i o e : FS.Stream) : IO Unit := do
  let mut workerPath ← IO.appPath
  if let some path := (←IO.getEnv "LEAN_SYSROOT") then
    workerPath := System.FilePath.mk path / "bin" / "lean" |>.withExtension System.FilePath.exeExtension
  if let some path := (←IO.getEnv "LEAN_WORKER_PATH") then
    workerPath := System.FilePath.mk path
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
        name     := "Lean 4 server"
        version? := "0.0.1"
      }
      : InitializeResult
    }
  }
  ReaderT.run initAndRunWatchdogAux {
    hIn            := i
    hOut           := o
    hLog           := e
    args           := args
    fileWorkersRef := fileWorkersRef
    initParams     := initRequest.param
    editDelay      := initRequest.param.initializationOptions? |>.bind InitializationOptions.editDelay? |>.getD 200
    workerPath     := workerPath
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
