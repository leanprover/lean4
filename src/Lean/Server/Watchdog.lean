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
- File workers will never receive a `shutdown` request or an `exit` notification. File workers are always terminated
  by closing their I/O channels. Similarly, they never receive a `didClose` notification.

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

/-- Things that can happen in a worker. -/
inductive WorkerEvent
| terminated
| crashed
| ioError (e : IO.Error)
-- TODO(WN): more things will be able to happen

structure FileWorker :=
(doc : OpenDocument)
(proc : Process.Child workerCfg)
(commTask : Task WorkerEvent)

namespace FileWorker

def stdin (fw : FileWorker) : FS.Stream :=
FS.Stream.ofHandle fw.proc.stdin

def stdout (fw : FileWorker) : FS.Stream :=
FS.Stream.ofHandle fw.proc.stdout

def stderr (fw : FileWorker) : FS.Stream :=
FS.Stream.ofHandle fw.proc.stderr

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
| none    => throw (userError $ "got unknown document URI (" ++ uri ++ ")")

-- TODO: this creates a long-running Task, which should be okay with upcoming API changes.
partial def fwdMsgAux (workerProc : Process.Child workerCfg) (hWrk : FS.Stream) (hOut : FS.Stream) : Unit → IO WorkerEvent
| ⟨⟩ => do
  catch 
    (do 
      msg ← readLspMessage hWrk;
      -- NOTE: Writes to Lean I/O channels are atomic, so these won't trample on each other.
      writeLspMessage hOut msg;
      fwdMsgAux ())
    (fun err => do
      exitCode ← workerProc.wait;
      -- Terminated events are always initiated by the main task, and should only
      -- occur when the main task already discarded the corresponding file worker.
      -- Specifically, after discarding, the main task will not listen to the 
      -- events of this forwarding task anymore.
      pure $ if exitCode = 0 then WorkerEvent.terminated else WorkerEvent.crashed)
    
/-- A Task which forwards a worker's messages into the output stream until an event
which must be handled in the main watchdog thread (e.g. an I/O error) happens. -/
def fwdMsgTask (workerProc : Process.Child workerCfg) (hWrk : FS.Stream) : ServerM (Task WorkerEvent) :=
fun st =>
  (Task.map (fun either => match either with
    | Except.ok ev   => ev
    | Except.error e => WorkerEvent.ioError e)) <$> (IO.asTask $ fwdMsgAux workerProc hWrk st.hOut ())

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
writeLspRequest (FS.Stream.ofHandle workerProc.stdin) (0 : Nat) "initialize" st.initParams;
writeLspNotification (FS.Stream.ofHandle workerProc.stdin) "textDocument/didOpen"
  (DidOpenTextDocumentParams.mk ⟨uri, "lean", version, text.source⟩);
commTask ← fwdMsgTask workerProc $ FS.Stream.ofHandle workerProc.stdout;
let fw : FileWorker := ⟨doc, workerProc, commTask⟩;
updateFileWorkers uri fw

def terminateFileWorker (uri : DocumentUri) : ServerM Unit :=
-- We're abusing the GC here. Erasing the file worker will free the stdin
-- handle of the subprocess, which will terminate as a result.
-- Upon terminating, the stdout handle is closed, which the 
-- forwarding task will detect and then terminate itself.
-- TODO(MH): emit ContentChanged errors for pending requests
-- to that file worker.
fun st => st.fileWorkersRef.modify (fun fileWorkers => fileWorkers.erase uri)
  
def parseParams (paramType : Type*) [HasFromJson paramType] (params : Json) : ServerM paramType :=
match fromJson? params with
| some parsed => pure parsed
| none        => throw (userError "got param with wrong structure")

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
some newVersion ← pure doc.version? | throw (userError "expected version number");
if newVersion <= oldDoc.version then do
  throw (userError "got outdated version number")
else changes.forM $ fun change =>
  match change with
  | TextDocumentContentChangeEvent.rangeChange (range : Range) (newText : String) => do
    let startOff := oldDoc.text.lspPosToUtf8Pos range.start;
    let newDocText := replaceLspRange oldDoc.text range newText;
    let oldHeaderEndPos := oldDoc.headerEndPos;
    if startOff < oldHeaderEndPos then do
      /- The header changed, restart worker. -/
      -- TODO(WN): we should amortize this somehow;
      -- when the user is typing in an import, this
      -- may rapidly destroy/create new processes
      terminateFileWorker doc.uri;
      startFileWorker doc.uri newVersion newDocText
    else
      let newDoc : OpenDocument := ⟨newVersion, newDocText, oldHeaderEndPos⟩;
      updateFileWorkers doc.uri { fw with doc := newDoc };
      writeLspNotification fw.stdin "textDocument/didChange" p
  | TextDocumentContentChangeEvent.fullChange (text : String) =>
    throw (userError "TODO impl computing the diff of two sources.")

def handleDidClose (p : DidCloseTextDocumentParams) : ServerM Unit := do
st ← read;
let doc := p.textDocument;
fw ← findFileWorker doc.uri;
terminateFileWorker doc.uri;
st.fileWorkersRef.modify (fun fileWorkers => fileWorkers.erase doc.uri)

def handleRequest (id : RequestID) (method : String) (params : Json) : ServerM Unit := do
let h := (fun α [HasFromJson α] [HasToJson α] [HasFileSource α] => do
           parsedParams ← parseParams α params;
           fw ← findFileWorker $ fileSource parsedParams;
           writeLspRequest fw.stdin id method parsedParams);
match method with
| "textDocument/hover" => h HoverParams
| _ => throw (userError $ "got unsupported request: " ++ method ++
                          "; params: " ++ toString params)

def handleNotification (method : String) (params : Json) : ServerM Unit := do
let forward := (fun α [HasFromJson α] [HasToJson α] [HasFileSource α] => do
                 parsedParams ← parseParams α params;
                 fw ← findFileWorker $ fileSource parsedParams;
                 writeLspNotification fw.stdin method parsedParams);
let handle := (fun α [HasFromJson α] (handler : α → ServerM Unit) => parseParams α params >>= handler);
match method with
| "textDocument/didOpen"   => handle DidOpenTextDocumentParams handleDidOpen
| "textDocument/didChange" => handle DidChangeTextDocumentParams handleDidChange
| "textDocument/didClose"  => handle DidCloseTextDocumentParams handleDidClose
| "$/cancelRequest"        => pure () -- TODO forward CancelParams
| _                        => throw (userError "got unsupported notification method")

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
  let clientTask := Task.map
    (fun either => match either with
    | Except.ok ev   => ev
    | Except.error e => ServerEvent.ClientError e)
    clientTask;

  let workerTasks := workers.fold
    (fun acc uri fw =>
    Task.map (ServerEvent.WorkerEvent uri fw) fw.commTask :: acc)
    ([] : List (Task ServerEvent));

  ev ← liftIO $ IO.waitAny $ clientTask :: workerTasks;

  match ev with
  | ServerEvent.ClientMsg msg => do
    match msg with
    | Message.request id "shutdown" _ =>
      writeLspResponse st.hOut id (Json.null)
    | Message.request id method (some params) => do
      handleRequest id method (toJson params);
      mainLoop ()
    | Message.notification method (some params) => do
      handleNotification method (toJson params);
      mainLoop ()
    | _ => throw (userError "got invalid JSON-RPC message")

  | ServerEvent.ClientError e => do
    pure () -- shutdown

  /- Restart an exited worker. -/
  | ServerEvent.WorkerEvent uri fw err =>
    match err with
    | WorkerEvent.ioError e => throw e -- shouldn't occur
    -- Cannot occur: Terminated events are only generated if the subprocess exits with exit code 0,
    -- which happens only if the file worker was terminated. But terminated file workers are not queried
    -- in the next waitAny cycle, and hence the HeaderChanged event will never reach the main task.
    | WorkerEvent.terminated => throw (userError "internal server error: got Terminated worker event")
    | WorkerEvent.crashed =>
      -- TODO restart fw in such a way that no restart loops occur
      mainLoop ()

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
_ ← readLspNotificationAs st.hIn "initialized" InitializedParams;
mainLoop ();
Message.notification "exit" none ← readLspMessage st.hIn
  | throw (userError "Expected an Exit Notification.");
pure ()

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
