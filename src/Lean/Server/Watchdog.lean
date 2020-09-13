/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Init.System.IO
import Std.Data.RBMap

import Lean.Elab.Import

import Lean.Data.Lsp
import Lean.Server.HasFileSource

/-!
For general server architecture, see `README.md`. This module implements the watchdog process.

## Watchdog state

Most LSP clients only send us file diffs, so to facilitate sending entire file contents to freshly restarted workers,
the watchdog needs to maintain the current state of each file. It can also use this state to detect changes
to the header and thus restart the corresponding worker, freeing its imports.

TODO(WN):
We may eventually want to keep track of approximately (since this isn't knowable exactly) where in the file a worker
crashed. Then on restart, we said worker to only parse up to that point and query the user about how to proceed
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

private def replaceLspRange (text : FileMap) (r : Lsp.Range) (newText : String) : FileMap :=
let start := text.lspPosToUtf8Pos r.start;
let «end» := text.lspPosToUtf8Pos r.«end»;
let pre := text.source.extract 0 start;
let post := text.source.extract «end» text.source.bsize;
(pre ++ newText ++ post).toFileMap

private def parsedImportsEndPos (input : String) : IO String.Pos := do
env ← mkEmptyEnvironment;
let fileName := "<input>";
let inputCtx := Parser.mkInputContext input fileName;
let (_, parserState, _) := Parser.parseHeader env inputCtx;
pure parserState.pos

structure EditableDocument :=
(version : Nat)
(text : FileMap)
(headerEndPos : String.Pos)

def workerCfg : Process.StdioConfig := ⟨Process.Stdio.piped, Process.Stdio.piped, Process.Stdio.piped⟩

structure FileWorker :=
(doc : EditableDocument)
(proc : Process.Child workerCfg)

namespace FileWorker

def spawnArgs : Process.SpawnArgs := {workerCfg with cmd := "fileworker"}

def spawn (doc : EditableDocument) : IO FileWorker := do
proc ← Process.spawn spawnArgs;
pure ⟨doc, proc⟩

def stdin (fw : FileWorker) : FS.Stream :=
FS.Stream.ofHandle fw.proc.stdin

def stdout (fw : FileWorker) : FS.Stream :=
FS.Stream.ofHandle fw.proc.stdout

def stderr (fw : FileWorker) : FS.Stream :=
FS.Stream.ofHandle fw.proc.stderr

def wait (w : FileWorker) : IO Nat := pure 0

end FileWorker

abbrev FileWorkerMap := RBMap DocumentUri FileWorker (fun a b => Decidable.decide (a < b))

structure ServerContext :=
(hIn hOut : FS.Stream)
(fileWorkersRef : IO.Ref FileWorkerMap)
(initParams : InitializeParams)

abbrev ServerM := ReaderT ServerContext IO

def updateFileWorkers (key : DocumentUri) (val : FileWorker) : ServerM Unit :=
fun st => st.fileWorkersRef.modify (fun fileWorkers => fileWorkers.insert key val)

def findFileWorker (key : DocumentUri) : ServerM FileWorker :=
fun st => do
fileWorkers ← st.fileWorkersRef.get;
match fileWorkers.find? key with
| some fw => pure fw
| none    => throw (userError $ "got unknown document URI (" ++ key ++ ")")

def readWorkerLspMessage (key : DocumentUri) : ServerM JsonRpc.Message :=
findFileWorker key >>= fun fw => monadLift $ readLspMessage fw.stdout

def readUserLspMessage : ServerM JsonRpc.Message :=
fun st => monadLift $ readLspMessage st.hIn

def readWorkerLspRequestAs (key : DocumentUri) (expectedMethod : String) (α : Type*) [HasFromJson α] : ServerM (Request α) :=
findFileWorker key >>= fun fw => monadLift $ readLspRequestAs fw.stdout expectedMethod α

def readUserLspRequestAs (expectedMethod : String) (α : Type*) [HasFromJson α] : ServerM (Request α) :=
fun st => monadLift $ readLspRequestAs st.hIn expectedMethod α

def readWorkerLspNotificationAs (key : DocumentUri) (expectedMethod : String) (α : Type*) [HasFromJson α] : ServerM α :=
findFileWorker key >>= fun fw => monadLift $ readLspNotificationAs fw.stdout expectedMethod α

def readUserLspNotificationAs (expectedMethod : String) (α : Type*) [HasFromJson α] : ServerM α :=
fun st => monadLift $ readLspNotificationAs st.hIn expectedMethod α

def writeWorkerLspMessage (key : DocumentUri) (msg : JsonRpc.Message) : ServerM Unit :=
findFileWorker key >>= fun fw => monadLift $ writeLspMessage fw.stdin msg

def writeUserLspMessage (msg : JsonRpc.Message) : ServerM Unit :=
fun st => monadLift $ writeLspMessage st.hOut msg

def writeWorkerLspRequest {α : Type*} [HasToJson α] (key : DocumentUri) (id : RequestID) (method : String) (params : α) : ServerM Unit :=
findFileWorker key >>= fun fw => monadLift $ writeLspRequest fw.stdin id method params

def writeUserLspRequest {α : Type*} [HasToJson α] (id : RequestID) (method : String) (params : α) : ServerM Unit :=
fun st => monadLift $ writeLspRequest st.hOut id method params

def writeWorkerLspNotification {α : Type*} [HasToJson α] (key : DocumentUri) (method : String) (params : α) : ServerM Unit :=
findFileWorker key >>= fun fw => monadLift $ writeLspNotification fw.stdin method params

def writeUserLspNotification {α : Type*} [HasToJson α] (method : String) (params : α) : ServerM Unit :=
fun st => monadLift $ writeLspNotification st.hOut method params

def writeWorkerLspResponse {α : Type*} [HasToJson α] (key : DocumentUri) (id : RequestID) (params : α) : ServerM Unit :=
findFileWorker key >>= fun fw => monadLift $ writeLspResponse fw.stdin id params

def writeUserLspResponse {α : Type*} [HasToJson α] (id : RequestID) (params : α) : ServerM Unit :=
fun st => monadLift $ writeLspResponse st.hOut id params

def writeWorkerInitializeParams (key : DocumentUri) : ServerM Unit := do
st ← read;
writeWorkerLspRequest key (0 : Nat) "initialize" st.initParams

def writeWorkerDidOpenNotification (key : DocumentUri) : ServerM Unit := do
findFileWorker key >>= fun fw => writeWorkerLspNotification key "textDocument/didOpen"
  (DidOpenTextDocumentParams.mk ⟨key, "lean", fw.doc.version, fw.doc.text.source⟩)

def parseParams (paramType : Type*) [HasFromJson paramType] (params : Json) : ServerM paramType :=
match fromJson? params with
| some parsed => pure parsed
| none        => throw (userError "got param with wrong structure")

-- NOTE(MH): forwardFileWorkerPackets needs to take a FileWorker, not a DocumentUri.
-- otherwise, it might occur that we update the list of file workers on the main task,
-- possibly yielding a race condition.
partial def forwardFileWorkerPackets (fw : FileWorker) : Unit → ServerM Unit
| ⟨⟩ => do
  -- TODO(MH): detect closed stream somehow and terminate gracefully
  -- TODO(MH): potentially catch unintended termination (e.g. due to stack overflow) and restart process
  msg ← monadLift $ readLspMessage fw.stdout;
  -- NOTE: Writes to Lean I/O streams are atomic, so we don't need to synchronise these in principle.
  writeUserLspMessage msg;
  forwardFileWorkerPackets ⟨⟩

def startFileWorker (key : DocumentUri) (version : Nat) (text : FileMap) : ServerM Unit := do
pos ← monadLift $ parsedImportsEndPos text.source;
fw ← monadLift $ FileWorker.spawn ⟨version, text, pos⟩;
updateFileWorkers key fw;
writeWorkerInitializeParams key;
writeWorkerDidOpenNotification key;
-- TODO(MH): replace with working IO variant
-- TODO(MH): Sebastian said something about this better being implemented as threads
-- (due to the long running nature of these tasks) but i did not yet have time to
-- look into this.
let _ := Task.mk (forwardFileWorkerPackets fw);
pure ⟨⟩

-- TODO(MH)
def terminateFileWorker (fw : FileWorker) : ServerM Unit := pure ()

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
      terminateFileWorker fw;
      startFileWorker doc.uri newVersion newDocText
    else
      let newDoc : EditableDocument := ⟨newVersion, newDocText, oldHeaderEndPos⟩;
      updateFileWorkers doc.uri { fw with doc := newDoc };
      writeWorkerLspNotification doc.uri "textDocument/didChange" p
  | TextDocumentContentChangeEvent.fullChange (text : String) =>
    throw (userError "TODO impl computing the diff of two sources.")

def handleDidClose (p : DidCloseTextDocumentParams) : ServerM Unit := do
let doc := p.textDocument;
fw ← findFileWorker doc.uri;
terminateFileWorker fw;
st ← read;
st.fileWorkersRef.modify (fun fileWorkers => fileWorkers.erase doc.uri)

def handleRequest (id : RequestID) (method : String) (params : Json) : ServerM Unit := do
let h := (fun α [HasFromJson α] [HasToJson α] [HasFileSource α] => do
           parsedParams ← parseParams α params;
           writeWorkerLspRequest (fileSource parsedParams) id method parsedParams);
match method with
| "textDocument/hover" => h HoverParams
| _ => throw (userError $ "got unsupported request: " ++ method ++
                          "; params: " ++ toString params)

def handleNotification (method : String) (params : Json) : ServerM Unit := do
let forward := (fun α [HasFromJson α] [HasToJson α] [HasFileSource α] => do
           parsedParams ← parseParams α params;
           writeWorkerLspNotification (fileSource parsedParams) method parsedParams);
let handle := (fun α [HasFromJson α] (handler : α → ServerM Unit) => parseParams α params >>= handler);
match method with
| "textDocument/didOpen"   => handle DidOpenTextDocumentParams handleDidOpen
| "textDocument/didChange" => handle DidChangeTextDocumentParams handleDidChange
| "textDocument/didClose"  => handle DidCloseTextDocumentParams handleDidClose
| "$/cancelRequest"        => pure () -- TODO when we're async
| _                        => throw (userError "got unsupported notification method")

partial def mainLoop : Unit → ServerM Unit
| () => do
  msg ← readUserLspMessage;
  match msg with
  | Message.request id "shutdown" _ =>
    writeUserLspResponse id (Json.null)
  | Message.request id method (some params) => do
    handleRequest id method (toJson params);
    mainLoop ()
  | Message.notification method (some params) => do
    handleNotification method (toJson params);
    mainLoop ()
  | _ => throw (userError "got invalid JSON-RPC message")

def mkLeanServerCapabilities : ServerCapabilities :=
{ textDocumentSync? := some
  { openClose := true,
    change := TextDocumentSyncKind.incremental,
    willSave := false,
    willSaveWaitUntil := false,
    save? := none },
  hoverProvider := true }

def initAndRunServer (i o : FS.Stream) : IO Unit := do
fileWorkersRef ← IO.mkRef (RBMap.empty : FileWorkerMap);
-- ignore InitializeParams for MWE
initRequest ← readLspRequestAs i "initialize" InitializeParams;
runReader
  (do
    writeUserLspResponse initRequest.id
      { capabilities := mkLeanServerCapabilities,
        serverInfo? := some { name := "Lean 4 server",
                              version? := "0.0.1" } : InitializeResult };
    _ ← readUserLspNotificationAs "initialized" InitializedParams;
    mainLoop ();
    Message.notification "exit" none ← readUserLspMessage
      | throw (userError "Expected an Exit Notification.");
    pure ())
  (⟨i, o, fileWorkersRef, initRequest.param⟩ : ServerContext)

end Server
end Lean
