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
import Lean.Server.HasFileSource
import Lean.Server.Utils

/-!
For general server architecture, see `README.md`. This module implements the watchdog process.

## Watchdog state

Most LSP clients only send us file diffs, so to facilitate sending entire file contents to freshly restarted workers,
the watchdog needs to maintain the current state of each file. It can also use this state to detect changes
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

- textDocument/didOpen: Launch the file worker, create the associated watchdog state and launch a task to asynchronously
                        receive LSP packets from the worker (e.g. request responses).
- textDocument/didChange: Update the local file state. If the header was mutated,
                          signal a shutdown to the file worker by closing the I/O channels.
                          Then restart the file worker. Otherwise, forward the `didChange` notification.
- textDocument/didClose: Signal a shutdown to the file worker and remove the associated watchdog state.

Moreover, we don't implement the full protocol at this level:

- Upon starting, the `initialize` request is forwarded to the worker, but it must not respond with its server capabilities.
  Consequently, the watchdog will not send an `initialized` notification to the worker.
- After `initialize`, the watchdog sends the corresponding `didOpen` notification with the full current state of the file.
  No additional `didOpen` notifications will be forwarded to the worker process.
- `$/cancelRequest` notifications are forwarded to all file workers.
- File workers are always terminated with an `exit` notification, without previously receiving a `shutdown` request. 
  Similarly, they never receive a `didClose` notification.

## Watchdog <-> client communication

The watchdog itself should implement the LSP standard as closely as possible. However we reserve the right to add non-standard
extensions in case they're needed, for example to communicate tactic state.
-/

namespace Lean
namespace Server

open IO
open Std (RBMap RBMap.empty)
open Lsp
open JsonRpc

structure OpenDocument :=
(version : Nat)
(text : FileMap)
(headerEndPos : String.Pos)

def workerCfg : Process.StdioConfig := ⟨Process.Stdio.piped, Process.Stdio.piped, Process.Stdio.piped⟩

-- Events that a forwarding task of a worker signals to the main task
inductive WorkerEvent
| terminated
| crashed (e : IO.Error)

inductive WorkerState
-- The watchdog can detect a crashed file worker in two places: When trying to send a message to the file worker and when reading a request reply.
-- In the latter case, the forwarding task terminates and delegates a `crashed` event to the main task. Then, in both cases, the
-- file worker has its state set to `crashed` and requests that are in-flight are errored. 
-- Upon receiving the next packet for that file worker, the file worker is restarted and the packet is forwarded to it.
-- If the crash was detected while writing a packet, we queue that packet until the next packet for the file worker arrives.
| crashed (queuedMsgs : Array JsonRpc.Message)
| running

abbrev PendingRequestMap := RBMap RequestID JsonRpc.Message (fun a b => Decidable.decide (a < b))

structure FileWorker :=
(doc : OpenDocument)
(proc : Process.Child workerCfg)
(commTask : Task WorkerEvent)
(state : WorkerState)
-- NOTE: this should not be mutated outside of namespace FileWorker
(pendingRequestsRef : IO.Ref PendingRequestMap)

namespace FileWorker

def stdin (fw : FileWorker) : FS.Stream :=
FS.Stream.ofHandle fw.proc.stdin

def stdout (fw : FileWorker) : FS.Stream :=
FS.Stream.ofHandle fw.proc.stdout

def stderr (fw : FileWorker) : FS.Stream :=
FS.Stream.ofHandle fw.proc.stderr

variables {m : Type → Type} [Monad m] [MonadIO m]

def readMessage (fw : FileWorker) : m JsonRpc.Message := do
msg ← readLspMessage fw.stdin;
match msg with
| Message.request id method params? => 
  liftIO $ fw.pendingRequestsRef.modify (fun pendingRequests => pendingRequests.erase id)
| _ => pure ();
pure msg

def writeMessage (fw : FileWorker) (msg : JsonRpc.Message) : m Unit :=
writeLspMessage fw.stdin msg

def writeNotification {α : Type*} [HasToJson α] (fw : FileWorker) (method : String) (param : α) : m Unit :=
writeLspNotification fw.stdin method param

def writeRequest {α : Type*} [HasToJson α] (fw : FileWorker) (id : RequestID) (method : String) (param : α) : m Unit := do
writeLspRequest fw.stdin id method param;
liftIO $ fw.pendingRequestsRef.modify $ fun pendingRequests => 
  pendingRequests.insert id (Message.request id method (fromJson? (toJson param)))

def errorPendingRequests (fw : FileWorker) (hOut : FS.Stream) (code : ErrorCode) (msg : String) : m Unit := do
pendingRequests ← liftIO $ fw.pendingRequestsRef.modifyGet (fun pendingRequests => (pendingRequests, RBMap.empty));
pendingRequests.forM (fun id _ => writeLspResponseError hOut id code msg)

end FileWorker

abbrev FileWorkerMap := RBMap DocumentUri FileWorker (fun a b => Decidable.decide (a < b))

structure ServerContext :=
(hIn hOut : FS.Stream)
(fileWorkersRef : IO.Ref FileWorkerMap)
/- We store these to pass them to workers. -/
(initParams : InitializeParams)
(workerPath : String)

abbrev ServerM := ReaderT ServerContext IO

def updateFileWorkers (uri : DocumentUri) (val : FileWorker) : ServerM Unit :=
fun st => st.fileWorkersRef.modify (fun fileWorkers => fileWorkers.insert uri val)

def findFileWorker (uri : DocumentUri) : ServerM FileWorker :=
fun st => do
fileWorkers ← st.fileWorkersRef.get;
match fileWorkers.find? uri with
| some fw => pure fw
| none    => throw (userError $ "Got unknown document URI (" ++ uri ++ ")")

def eraseFileWorker (uri : DocumentUri) : ServerM Unit :=
fun st => st.fileWorkersRef.modify (fun fileWorkers => fileWorkers.erase uri)

-- TODO: this creates a long-running Task, which should be okay with upcoming API changes.
partial def fwdMsgAux (fw : FileWorker) (hOut : FS.Stream) : Unit → IO WorkerEvent
| ⟨⟩ => catch 
    (do
      msg ← fw.readMessage;
      -- NOTE: Writes to Lean I/O channels are atomic, so these won't trample on each other.
      writeLspMessage hOut msg;
      fwdMsgAux ())
    (fun err => do
      -- NOTE: if writeLspMessage errors we will block here, but the main task will
      -- quit eventually anyways if that happens
      exitCode ← fw.proc.wait;
      if exitCode = 0 then do
        -- worker was terminated
        fw.errorPendingRequests hOut ErrorCode.contentModified "File header changed or file was closed";
        pure WorkerEvent.terminated 
      else do
        -- worker crashed
        fw.errorPendingRequests hOut ErrorCode.internalError "Server process of file crashed, likely due to a stack overflow in user code";
        pure (WorkerEvent.crashed err))
    
/-- A Task which forwards a worker's messages into the output stream until an event
which must be handled in the main watchdog thread (e.g. an I/O error) happens. -/
def fwdMsgTask (fw : FileWorker) : ServerM (Task WorkerEvent) :=
fun st =>
  (Task.map (fun either => match either with
    | Except.ok ev   => ev
    | Except.error e => WorkerEvent.crashed e)) <$> (IO.asTask (fwdMsgAux fw st.hOut ()) Task.Priority.dedicated)

private def parsedImportsEndPos (input : String) : IO String.Pos := do
emptyEnv ← mkEmptyEnvironment;
let inputCtx := Parser.mkInputContext input "<input>";
let (_, parserState, _) := Parser.parseHeader emptyEnv inputCtx;
pure parserState.pos

def startFileWorker (uri : DocumentUri) (version : Nat) (text : FileMap) : ServerM Unit := do
st ← read;
pos ← monadLift $ parsedImportsEndPos text.source;
let doc : OpenDocument := ⟨version, text, pos⟩;
workerProc ← monadLift $ Process.spawn {workerCfg with cmd := st.workerPath};
pendingRequestsRef ← IO.mkRef (RBMap.empty : PendingRequestMap);
-- the task will never access itself, so this is fine
let commTaskFw : FileWorker := ⟨doc, workerProc, Task.pure WorkerEvent.terminated, WorkerState.running, pendingRequestsRef⟩;
commTask ← fwdMsgTask commTaskFw;
let fw : FileWorker := {commTaskFw with commTask := commTask};
fw.writeRequest (0 : Nat) "initialize" st.initParams;
fw.writeNotification "textDocument/didOpen" (DidOpenTextDocumentParams.mk ⟨uri, "lean", version, text.source⟩);
updateFileWorkers uri fw

def terminateFileWorker (uri : DocumentUri) : ServerM Unit := do
fw ← findFileWorker uri;
-- the file worker must have crashed just when we were about to terminate it!
-- that's fine - just forget about it then.
-- (on didClose we won't need the crashed file worker anymore,
-- when the header changed we'll start a new one right after
-- anyways and when we're shutting down the server
-- it's over either way.)
catch (fw.writeMessage (Message.notification "exit" none)) (fun err => pure ());
eraseFileWorker uri
  
def parseParams (paramType : Type*) [HasFromJson paramType] (params : Json) : ServerM paramType :=
match fromJson? params with
| some parsed => pure parsed
| none        => throw (userError "Got param with wrong structure")

def handleCrash (uri : DocumentUri) (fw : FileWorker) (queuedMsgs : Array JsonRpc.Message) : ServerM Unit := do
fw ← findFileWorker uri;
updateFileWorkers uri {fw with state := WorkerState.crashed queuedMsgs}

def restartCrashedFileWorker (uri : DocumentUri) (fw : FileWorker) (queuedMsgs : Array JsonRpc.Message) : ServerM Unit := do
eraseFileWorker uri;
startFileWorker uri fw.doc.version fw.doc.text;
newFw ← findFileWorker uri;
let tryDischargeQueuedMsgs : Array JsonRpc.Message → JsonRpc.Message → ServerM (Array JsonRpc.Message) := 
  fun crashedMsgs m => catch 
    (do
      newFw.writeMessage m;
      pure crashedMsgs) 
    (fun err => pure (crashedMsgs.push m));
crashedMsgs ← queuedMsgs.foldlM tryDischargeQueuedMsgs #[];
if ¬ crashedMsgs.isEmpty then do
  handleCrash uri newFw crashedMsgs
else
  pure ()

def handleDidOpen (p : DidOpenTextDocumentParams) : ServerM Unit :=
let doc := p.textDocument;
-- NOTE(WN): `toFileMap` marks line beginnings as immediately following
-- "\n", which should be enough to handle both LF and CRLF correctly.
-- This is because LSP always refers to characters by (line, column),
-- so if we get the line number correct it shouldn't matter that there
-- is a CR there.
startFileWorker doc.uri doc.version doc.text.toFileMap

def handleDidChange (p : DidChangeTextDocumentParams) : ServerM Unit := do
let doc := p.textDocument;
let changes := p.contentChanges;
fw ← findFileWorker doc.uri;
let oldDoc := fw.doc;
some newVersion ← pure doc.version? | throw (userError "Expected version number");
if newVersion <= oldDoc.version then do
  throw (userError "Got outdated version number")
else match changes.get? 0 with
| none => pure ()
| some firstChange => do
  let firstStartOff := match firstChange with
    | TextDocumentContentChangeEvent.rangeChange (range : Range) _ => 
      oldDoc.text.lspPosToUtf8Pos range.start
    | TextDocumentContentChangeEvent.fullChange _ => 0;
  let accumulateChanges : TextDocumentContentChangeEvent → FileMap × String.Pos → FileMap × String.Pos :=
    fun change ⟨newDocText, minStartOff⟩ =>
      match change with
      | TextDocumentContentChangeEvent.rangeChange (range : Range) (newText : String) =>
        let startOff    := oldDoc.text.lspPosToUtf8Pos range.start;
        let newDocText  := replaceLspRange newDocText range newText;
        let minStartOff := if startOff < minStartOff then startOff else minStartOff;
        ⟨newDocText, minStartOff⟩
      | TextDocumentContentChangeEvent.fullChange (newText : String) =>
        ⟨newText.toFileMap, 0⟩;
  let (newDocText, minStartOff) := changes.foldr accumulateChanges (oldDoc.text, firstStartOff);
  let oldHeaderEndPos := oldDoc.headerEndPos;
  if minStartOff < oldHeaderEndPos then do
    -- TODO(WN): we should amortize this somehow;
    -- when the user is typing in an import, this
    -- may rapidly destroy/create new processes
    terminateFileWorker doc.uri;
    startFileWorker doc.uri newVersion newDocText
  else do
    let newDoc : OpenDocument := ⟨newVersion, newDocText, oldHeaderEndPos⟩;
    let newFw : FileWorker := {fw with doc := newDoc};
    updateFileWorkers doc.uri newFw;
    let msg := Message.notification "textDocument/didChange" (fromJson? (toJson p));
    match fw.state with
    | WorkerState.crashed queuedMsgs => restartCrashedFileWorker doc.uri newFw (queuedMsgs.push msg)
    | WorkerState.running =>
      -- looks like it crashed now!
      catch (fw.writeNotification "textDocument/didChange" p)
            (fun err => handleCrash doc.uri newFw #[msg])

def handleDidClose (p : DidCloseTextDocumentParams) : ServerM Unit :=
terminateFileWorker p.textDocument.uri

def handleCancelRequest (p : CancelParams) : ServerM Unit := do
st ← read;
fileWorkers ← st.fileWorkersRef.get;
fileWorkers.forM (fun _ fw => fw.writeNotification "$/cancelParams" p)

def handleRequest (id : RequestID) (method : String) (params : Json) : ServerM Unit := do
let h := (fun α [HasFromJson α] [HasToJson α] [HasFileSource α] => do
           parsedParams ← parseParams α params;
           let uri := fileSource parsedParams;
           fw ← findFileWorker uri;
           let msg := Message.request id method (fromJson? params);
           match fw.state with
           | WorkerState.crashed queuedMsgs => restartCrashedFileWorker uri fw (queuedMsgs.push msg)
           | WorkerState.running => do
             -- if this errors, the file worker crashed
             catch (fw.writeRequest id method parsedParams) 
                   (fun err => handleCrash uri fw #[msg]));
match method with
| "textDocument/hover" => h HoverParams
| _ => throw (userError $ "Got unsupported request: " ++ method ++
                          "; params: " ++ toString params)

def handleNotification (method : String) (params : Json) : ServerM Unit := do
let handle := (fun α [HasFromJson α] (handler : α → ServerM Unit) => parseParams α params >>= handler);
match method with
| "textDocument/didOpen"   => handle DidOpenTextDocumentParams handleDidOpen
| "textDocument/didChange" => handle DidChangeTextDocumentParams handleDidChange
| "textDocument/didClose"  => handle DidCloseTextDocumentParams handleDidClose
| "$/cancelRequest"        => handle CancelParams handleCancelRequest
| _                        => throw (userError "Got unsupported notification method")

def shutdown : ServerM Unit := do
st ← read;
fileWorkers ← st.fileWorkersRef.get;
fileWorkers.forM (fun id _ => terminateFileWorker id)

inductive ServerEvent
| WorkerEvent (uri : DocumentUri) (fw : FileWorker) (ev : WorkerEvent)
| ClientMsg (msg : JsonRpc.Message)
| ClientError (e : IO.Error)

partial def mainLoop : Unit → ServerM Unit
| () => do
  st ← read;
  workers ← st.fileWorkersRef.get;

  /- Wait for any of the following events to happen:
     - client sends us a message
     - a worker does something -/
  clientTask ← liftIO $ IO.asTask $ ServerEvent.ClientMsg <$> readLspMessage st.hIn;
  let clientTask := clientTask.map
    (fun either => match either with
    | Except.ok ev   => ev
    | Except.error e => ServerEvent.ClientError e);

  let workerTasks := workers.fold
    (fun acc uri fw =>
      fw.commTask.map (ServerEvent.WorkerEvent uri fw) :: acc)
    ([] : List (Task ServerEvent));

  ev ← liftIO $ IO.waitAny $ clientTask :: workerTasks;

  match ev with
  | ServerEvent.ClientMsg msg => do
    match msg with
    | Message.request id "shutdown" _ => do
      shutdown;
      writeLspResponse st.hOut id (Json.null)
    | Message.request id method (some params) => do
      handleRequest id method (toJson params);
      mainLoop ()
    | Message.notification method (some params) => do
      handleNotification method (toJson params);
      mainLoop ()
    | _ => throw (userError "Got invalid JSON-RPC message")

  | ServerEvent.ClientError e =>
    shutdown

  /- Restart an exited worker. -/
  | ServerEvent.WorkerEvent uri fw err =>
    match err with
    | WorkerEvent.crashed e => handleCrash uri fw #[]
    | WorkerEvent.terminated => throw (userError "Internal server error: got termination event for worker that should have been removed")

def mkLeanServerCapabilities : ServerCapabilities :=
{ textDocumentSync? := some
  { openClose := true,
    change := TextDocumentSyncKind.incremental,
    willSave := false,
    willSaveWaitUntil := false,
    save? := none },
  hoverProvider := true }

def initAndRunWatchdogAux : ServerM Unit := do
st ← read;
catch 
  (do
    _ ← readLspNotificationAs st.hIn "initialized" InitializedParams;
    mainLoop ();
    Message.notification "exit" none ← readLspMessage st.hIn
    | throw (userError "Expected an exit notification");
    pure ()) 
  -- something crashed, try to terminate all the file workers and all the forwarding tasks
  -- so that we can die in peace
  (fun err => do shutdown; throw err)


def initAndRunWatchdog (i o : FS.Stream) : IO Unit := do
some workerPath ← IO.getEnv "LEAN_WORKER_PATH"
  | throw $ userError "You need to specify LEAN_WORKER_PATH in the environment.";
fileWorkersRef ← IO.mkRef (RBMap.empty : FileWorkerMap);

initRequest ← readLspRequestAs i "initialize" InitializeParams;
writeLspResponse o initRequest.id
  { capabilities := mkLeanServerCapabilities,
    serverInfo? := some { name := "Lean 4 server",
                          version? := "0.0.1" } : InitializeResult };

runReader
  initAndRunWatchdogAux
  (⟨i, o, fileWorkersRef, initRequest.param, workerPath⟩ : ServerContext)

end Server
end Lean

def main (_ : List String) : IO UInt32 := do
i ← IO.getStdin;
o ← IO.getStdout;
e ← IO.getStderr;
Lean.initSearchPath;
catch
  (Lean.Server.initAndRunWatchdog i o)
  (fun err => e.putStrLn (toString err));
pure 0
