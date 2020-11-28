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
the worker could get into a restart loop.

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

namespace Lean
namespace Server

open IO
open Std (RBMap RBMap.empty)
open Lsp
open JsonRpc
open System.FilePath

structure OpenDocument where
  version : Nat
  text : FileMap
  headerAst : Syntax

def workerCfg : Process.StdioConfig :=
  { stdin  := Process.Stdio.piped,
    stdout := Process.Stdio.piped,
    /- The watchdog doesn't read workers' stderr,
    so we let it be null so as to not overfill a pipe. -/
    stderr := Process.Stdio.null }

-- Events that a forwarding task of a worker signals to the main task
inductive WorkerEvent where
  | terminated
  | crashed (e : IO.Error)

inductive WorkerState where
  -- The watchdog can detect a crashed file worker in two places: When trying to send a message to the file worker
  -- and when reading a request reply.
  -- In the latter case, the forwarding task terminates and delegates a `crashed` event to the main task.
  -- Then, in both cases, the file worker has its state set to `crashed` and requests that are in-flight are errored.
  -- Upon receiving the next packet for that file worker, the file worker is restarted and the packet is forwarded
  -- to it. If the crash was detected while writing a packet, we queue that packet until the next packet for the file
  -- worker arrives.
  | crashed (queuedMsgs : Array JsonRpc.Message)
  | running

abbrev PendingRequestMap := RBMap RequestID JsonRpc.Message (fun a b => Decidable.decide (a < b))

structure FileWorker where
  doc : OpenDocument
  proc : Process.Child workerCfg
  commTask : Task WorkerEvent
  state : WorkerState
  -- NOTE: this should not be mutated outside of namespace FileWorker
  pendingRequestsRef : IO.Ref PendingRequestMap

namespace FileWorker

def stdin (fw : FileWorker) : FS.Stream :=
  FS.Stream.ofHandle fw.proc.stdin

def stdout (fw : FileWorker) : FS.Stream :=
  FS.Stream.ofHandle fw.proc.stdout

def readMessage (fw : FileWorker) : IO JsonRpc.Message := do
  let msg ← readLspMessage fw.stdout
  match msg with
  | Message.request id method params? =>
    fw.pendingRequestsRef.modify (fun pendingRequests => pendingRequests.erase id)
  | _ => ()
  msg

def writeMessage (fw : FileWorker) (msg : JsonRpc.Message) : IO Unit :=
  writeLspMessage fw.stdin msg

def writeNotification [ToJson α] (fw : FileWorker) (method : String) (param : α) : IO Unit :=
  writeLspNotification fw.stdin method param

def writeRequest [ToJson α] (fw : FileWorker) (id : RequestID) (method : String) (param : α) : IO Unit := do
  writeLspRequest fw.stdin id method param
  fw.pendingRequestsRef.modify $ fun pendingRequests =>
    pendingRequests.insert id (Message.request id method (Json.toStructured? param))

def errorPendingRequests (fw : FileWorker) (hOut : FS.Stream) (code : ErrorCode) (msg : String) : IO Unit := do
  let pendingRequests ← fw.pendingRequestsRef.modifyGet (fun pendingRequests => (pendingRequests, RBMap.empty))
  pendingRequests.forM (fun id _ => writeLspResponseError hOut id code msg)

end FileWorker

abbrev FileWorkerMap := RBMap DocumentUri FileWorker (fun a b => Decidable.decide (a < b))

structure ServerContext where
  hIn hOut : FS.Stream
  hLog : FS.Stream
  fileWorkersRef : IO.Ref FileWorkerMap
  /- We store these to pass them to workers. -/
  initParams : InitializeParams
  workerPath : String

abbrev ServerM := ReaderT ServerContext IO

def updateFileWorkers (uri : DocumentUri) (val : FileWorker) : ServerM Unit :=
  fun st => st.fileWorkersRef.modify (fun fileWorkers => fileWorkers.insert uri val)

def findFileWorker (uri : DocumentUri) : ServerM FileWorker :=
  fun st => do
    match (←st.fileWorkersRef.get).find? uri with
    | some fw => fw
    | none    => throwServerError $ "Got unknown document URI (" ++ uri ++ ")"

def eraseFileWorker (uri : DocumentUri) : ServerM Unit :=
  fun st => st.fileWorkersRef.modify (fun fileWorkers => fileWorkers.erase uri)

def log (msg : String) : ServerM Unit :=
  fun st => do
    st.hLog.putStrLn msg
    st.hLog.flush

/-- A Task which forwards a worker's messages into the output stream until an event
which must be handled in the main watchdog thread (e.g. an I/O error) happens. -/
partial def fwdMsgTask (fw : FileWorker) : ServerM (Task WorkerEvent) := do
  let o := (←read).hOut
  let rec loop : IO WorkerEvent := do
    try
      let msg ← fw.readMessage
      -- NOTE: Writes to Lean I/O channels are atomic, so these won't trample on each other.
      writeLspMessage o msg
      loop
    catch err =>
      -- NOTE: if writeLspMessage from above errors we will block here, but the main task will
      -- quit eventually anyways if that happens
      let exitCode ← fw.proc.wait
      if exitCode = 0 then
        -- worker was terminated
        fw.errorPendingRequests o ErrorCode.contentModified "File header changed or file was closed"
        WorkerEvent.terminated
      else
        -- worker crashed
        fw.errorPendingRequests o ErrorCode.internalError
          "Server process of file crashed, likely due to a stack overflow in user code"
        WorkerEvent.crashed err
  let task ← IO.asTask loop Task.Priority.dedicated
  task.map $ fun
    | Except.ok ev   => ev
    | Except.error e => WorkerEvent.crashed e

private def parseHeaderAst (input : String) : IO Syntax := do
  let inputCtx   := Parser.mkInputContext input "<input>"
  let (stx, _, _) ← Parser.parseHeader inputCtx
  stx

def startFileWorker (uri : DocumentUri) (version : Nat) (text : FileMap) : ServerM Unit := do
  let st ← read
  let headerAst ← parseHeaderAst text.source
  let workerProc ← Process.spawn { toStdioConfig := workerCfg, cmd := st.workerPath }
  let pendingRequestsRef ← IO.mkRef (RBMap.empty : PendingRequestMap)
  -- the task will never access itself, so this is fine
  let commTaskFw : FileWorker := {
    doc                := ⟨version, text, headerAst⟩
    proc               := workerProc
    commTask           := Task.pure WorkerEvent.terminated
    state              := WorkerState.running
    pendingRequestsRef := pendingRequestsRef
  }
  let commTask ← fwdMsgTask commTaskFw
  let fw : FileWorker := { commTaskFw with commTask := commTask }
  writeLspRequest fw.stdin (0 : Nat) "initialize" st.initParams
  fw.writeNotification "textDocument/didOpen" {
    textDocument := {
      uri        := uri
      languageId := "lean"
      version    := version
      text       := text.source
    } : DidOpenTextDocumentParams
  }
  updateFileWorkers uri fw

def terminateFileWorker (uri : DocumentUri) : ServerM Unit := do
  -- the file worker must have crashed just when we were about to terminate it!
  -- that's fine - just forget about it then.
  -- (on didClose we won't need the crashed file worker anymore,
  -- when the header changed we'll start a new one right after
  -- anyways and when we're shutting down the server
  -- it's over either way.)
  try (←findFileWorker uri).writeMessage (Message.notification "exit" none)
  catch err => ()
  eraseFileWorker uri

def parseParams (paramType : Type) [FromJson paramType] (params : Json) : ServerM paramType :=
  match fromJson? params with
  | some parsed => pure parsed
  | none        => throwServerError $ "Got param with wrong structure: " ++ params.compress

def handleCrash (uri : DocumentUri) (queuedMsgs : Array JsonRpc.Message) : ServerM Unit := do
  updateFileWorkers uri { ←findFileWorker uri with state := WorkerState.crashed queuedMsgs }

def restartCrashedFileWorker (uri : DocumentUri) (fw : FileWorker) (queuedMsgs : Array JsonRpc.Message)
: ServerM Unit := do
  eraseFileWorker uri
  startFileWorker uri fw.doc.version fw.doc.text
  let newFw ← findFileWorker uri
  let mut crashedMsgs := #[]
  -- try to discharge all queued msgs, tracking the crashed ones
  for msg in queuedMsgs do
    try
      newFw.writeMessage msg
    catch _ =>
      crashedMsgs := crashedMsgs.push msg
  if ¬ crashedMsgs.isEmpty then
    handleCrash uri crashedMsgs

def handleDidOpen (p : DidOpenTextDocumentParams) : ServerM Unit :=
  let doc := p.textDocument
  -- NOTE(WN): `toFileMap` marks line beginnings as immediately following
  -- "\n", which should be enough to handle both LF and CRLF correctly.
  -- This is because LSP always refers to characters by (line, column),
  -- so if we get the line number correct it shouldn't matter that there
  -- is a CR there.
  startFileWorker doc.uri doc.version doc.text.toFileMap

def handleDidChange (p : DidChangeTextDocumentParams) : ServerM Unit := do
  let doc := p.textDocument
  let changes := p.contentChanges
  let fw ← findFileWorker doc.uri
  let oldDoc := fw.doc
  let some newVersion ← pure doc.version?
    | throwServerError "Expected version number"
  if newVersion <= oldDoc.version then
    throwServerError "Got outdated version number"
  if ¬ changes.isEmpty then
    let (newDocText, _) := foldDocumentChanges changes oldDoc.text
    let newHeaderAst ← parseHeaderAst newDocText.source
    if newHeaderAst != oldDoc.headerAst then
      -- TODO(WN): we should amortize this somehow
      -- when the user is typing in an import, this
      -- may rapidly destroy/create new processes
      terminateFileWorker doc.uri
      startFileWorker doc.uri newVersion newDocText
    else
      let newDoc : OpenDocument := ⟨newVersion, newDocText, oldDoc.headerAst⟩
      let newFw : FileWorker := { fw with doc := newDoc }
      updateFileWorkers doc.uri newFw
      let msg := Message.notification "textDocument/didChange" (Json.toStructured? p)
      match fw.state with
      | WorkerState.crashed queuedMsgs => restartCrashedFileWorker doc.uri newFw (queuedMsgs.push msg)
      | WorkerState.running =>
        try fw.writeNotification "textDocument/didChange" p
        catch _ => handleCrash doc.uri #[msg]

def handleDidClose (p : DidCloseTextDocumentParams) : ServerM Unit :=
  terminateFileWorker p.textDocument.uri

def handleCancelRequest (p : CancelParams) : ServerM Unit := do
  let fileWorkers ← (←read).fileWorkersRef.get
  fileWorkers.forM $ fun uri fw =>
    match fw.state with
    | WorkerState.crashed queuedMsgs => restartCrashedFileWorker uri fw queuedMsgs
    | WorkerState.running =>
      try fw.writeNotification "$/cancelRequest" p
      catch _ => handleCrash uri #[]

def handleRequest (id : RequestID) (method : String) (params : Json) : ServerM Unit := do
  let handle := fun α [FromJson α] [ToJson α] [FileSource α] => do
    let parsedParams ← parseParams α params
    let uri := fileSource parsedParams
    let fw ← findFileWorker uri
    let msg := Message.request id method (fromJson? params)
    match fw.state with
    | WorkerState.crashed queuedMsgs => restartCrashedFileWorker uri fw (queuedMsgs.push msg)
    | WorkerState.running =>
      try fw.writeRequest id method parsedParams
      catch _ => handleCrash uri #[msg]
  match method with
  | "textDocument/hover" => handle HoverParams
  | _ => throwServerError $ "Got unsupported request: " ++ method ++ " params: " ++ toString params

def handleNotification (method : String) (params : Json) : ServerM Unit :=
  let handle := (fun α [FromJson α] (handler : α → ServerM Unit) => parseParams α params >>= handler)
  match method with
  | "textDocument/didOpen"   => handle DidOpenTextDocumentParams handleDidOpen
  | "textDocument/didChange" => handle DidChangeTextDocumentParams handleDidChange
  | "textDocument/didClose"  => handle DidCloseTextDocumentParams handleDidClose
  | "$/cancelRequest"        => handle CancelParams handleCancelRequest
  | _                        => throwServerError "Got unsupported notification method"

def shutdown : ServerM Unit := do
  let fileWorkers ← (←read).fileWorkersRef.get
  fileWorkers.forM (fun id _ => terminateFileWorker id)
  fileWorkers.forM (fun _ fw => do let _ ← IO.wait fw.commTask)

inductive ServerEvent where
  | WorkerEvent (uri : DocumentUri) (fw : FileWorker) (ev : WorkerEvent)
  | ClientMsg (msg : JsonRpc.Message)
  | ClientError (e : IO.Error)

def runClientTask : ServerM (Task ServerEvent) := do
  let readMsg : IO ServerEvent := ServerEvent.ClientMsg (←readLspMessage (←read).hIn)
  let clientTask ← (←IO.asTask readMsg).map $ fun
    | Except.ok ev   => ev
    | Except.error e => ServerEvent.ClientError e
  clientTask

partial def mainLoop (clientTask : Task ServerEvent) : ServerM Unit := do
  let st ← read
  let workers ← st.fileWorkersRef.get
  let workerTasks := workers.fold
    (fun acc uri fw =>
      match fw.state with
      | WorkerState.running => fw.commTask.map (ServerEvent.WorkerEvent uri fw) :: acc
      | _                   => acc)
    ([] : List (Task ServerEvent))
  let ev ← IO.waitAny $ clientTask :: workerTasks
  match ev with
  | ServerEvent.ClientMsg msg =>
    match msg with
    | Message.request id "shutdown" _ =>
      shutdown
      writeLspResponse st.hOut id Json.null
    | Message.request id method (some params) =>
      handleRequest id method (toJson params)
      let newClientTask ← runClientTask
      mainLoop newClientTask
    | Message.notification method (some params) =>
      handleNotification method (toJson params)
      let newClientTask ← runClientTask
      mainLoop newClientTask
    | _ => throwServerError "Got invalid JSON-RPC message"
  | ServerEvent.ClientError e => throw e
  | ServerEvent.WorkerEvent uri fw err =>
    match err with
    | WorkerEvent.crashed e =>
      handleCrash uri #[]
      mainLoop clientTask
    | WorkerEvent.terminated => throwServerError "Internal server error: got termination event for worker that should have been removed"

def mkLeanServerCapabilities : ServerCapabilities :=
  { textDocumentSync? := some
      { openClose := true
        change := TextDocumentSyncKind.incremental
        willSave := false
        willSaveWaitUntil := false
        save? := none }
    hoverProvider := true }

def initAndRunWatchdogAux : ServerM Unit := do
  let st ← read
  try
    let _ ← readLspNotificationAs st.hIn "initialized" InitializedParams
    let clientTask ← runClientTask
    mainLoop clientTask
    let Message.notification "exit" none ← readLspMessage st.hIn
      | throwServerError "Expected an exit notification"
   catch err =>
     shutdown
     throw err

def initAndRunWatchdog (i o e : FS.Stream) : IO Unit := do
  let workerPath ← IO.getEnv "LEAN_WORKER_PATH"
  let appDir ← IO.appDir
  let workerPath := match workerPath with
    | none   => appDir ++ pathSeparator.toString ++ "FileWorker" ++ exeSuffix
    | some p => p
  let fileWorkersRef ← IO.mkRef (RBMap.empty : FileWorkerMap)
  let i ← maybeTee "wdIn.txt" false i
  let o ← maybeTee "wdOut.txt" true o
  let e ← maybeTee "wdErr.txt" true e
  let initRequest ← readLspRequestAs i "initialize" InitializeParams
  writeLspResponse o initRequest.id
    { capabilities := mkLeanServerCapabilities,
      serverInfo?  := some { name     := "Lean 4 server"
                             version? := "0.0.1" }
      : InitializeResult }
  ReaderT.run
    initAndRunWatchdogAux
    { hIn            := i
      hOut           := o
      hLog           := e
      fileWorkersRef := fileWorkersRef
      initParams     := initRequest.param
      workerPath     := workerPath
      : ServerContext }

namespace Test

def runWatchdogWithInputFile (fn : String) (searchPath : Option String) : IO Unit := do
  let o ← IO.getStdout
  let e ← IO.getStderr
  FS.withFile fn FS.Mode.read $ fun hFile => do
    Lean.initSearchPath searchPath
    try Lean.Server.initAndRunWatchdog (FS.Stream.ofHandle hFile) o e
    catch err => e.putStrLn (toString err)

end Test
end Server
end Lean

-- TODO: compile separately OR add as a flag to the `lean` binary in order to stop
-- polluting the global symbol list with a `main` (and ditto in FileWorker.lean)
def main (args : List String) : IO UInt32 := do
  let i ← IO.getStdin
  let o ← IO.getStdout
  let e ← IO.getStderr
  Lean.initSearchPath
  try Lean.Server.initAndRunWatchdog i o e
  catch err => e.putStrLn (toString err)
  pure 0
