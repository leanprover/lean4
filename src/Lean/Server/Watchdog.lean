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
import Lean.Server.Utils

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

structure OpenDocument :=
(version : Nat)
(text : FileMap)
(headerEndPos : String.Pos)

def workerCfg : Process.StdioConfig := ⟨Process.Stdio.piped, Process.Stdio.piped, Process.Stdio.piped⟩

structure FileWorker :=
(doc : OpenDocument)
(proc : Process.Child workerCfg)

namespace FileWorker

def stdin (fw : FileWorker) : FS.Stream :=
FS.Stream.ofHandle fw.proc.stdin

def stdout (fw : FileWorker) : FS.Stream :=
FS.Stream.ofHandle fw.proc.stdout

def stderr (fw : FileWorker) : FS.Stream :=
FS.Stream.ofHandle fw.proc.stderr

def wait (fw : FileWorker) : IO Nat := pure 0 -- TODO

end FileWorker

abbrev FileWorkerMap := RBMap DocumentUri FileWorker (fun a b => Decidable.decide (a < b))

structure ServerContext :=
(hIn hOut : FS.Stream)
(fileWorkersRef : IO.Ref FileWorkerMap)
/- We store these to pass them to workers. -/
(initParams : InitializeParams)
(workerPath : String)

abbrev ServerM := ReaderT ServerContext IO

def spawnFileWorker (doc : OpenDocument) : ServerM FileWorker :=
fun st => do
  proc ← Process.spawn {workerCfg with cmd := st.workerPath};
  pure ⟨doc, proc⟩

def updateFileWorkers (uri : DocumentUri) (val : FileWorker) : ServerM Unit :=
fun st => st.fileWorkersRef.modify (fun fileWorkers => fileWorkers.insert uri val)

def findFileWorker (uri : DocumentUri) : ServerM FileWorker :=
fun st => do
fileWorkers ← st.fileWorkersRef.get;
match fileWorkers.find? uri with
| some fw => pure fw
| none    => throw (userError $ "got unknown document URI (" ++ uri ++ ")")

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
  msg ← readLspMessage fw.stdout;
  writeLspMessage fw.stdin msg;
  forwardFileWorkerPackets ⟨⟩

private def parsedImportsEndPos (input : String) : IO String.Pos := do
emptyEnv ← mkEmptyEnvironment; -- TODO(WN): a lot of things could be purified if `mkEmptyEnvironment` was just a pure ctr
let inputCtx := Parser.mkInputContext input "<input>";
let (_, parserState, _) := Parser.parseHeader emptyEnv inputCtx;
pure parserState.pos

def startFileWorker (uri : DocumentUri) (version : Nat) (text : FileMap) : ServerM Unit := do
st ← read;
pos ← monadLift $ parsedImportsEndPos text.source;
fw ← spawnFileWorker ⟨version, text, pos⟩;
writeLspRequest fw.stdin (0 : Nat) "initialize" st.initParams;
writeLspNotification fw.stdin "textDocument/didOpen"
  (DidOpenTextDocumentParams.mk ⟨uri, "lean", fw.doc.version, fw.doc.text.source⟩);
updateFileWorkers uri fw;
-- TODO(MH): replace with working IO variant
-- TODO(MH): Sebastian said something about this better being implemented as threads
-- (due to the long running nature of these tasks) but i did not yet have time to
-- look into this.
let _ := Task.pure (forwardFileWorkerPackets fw);
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
      let newDoc : OpenDocument := ⟨newVersion, newDocText, oldHeaderEndPos⟩;
      updateFileWorkers doc.uri { fw with doc := newDoc };
      writeLspNotification fw.stdin "textDocument/didChange" p
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
| "$/cancelRequest"        => pure () -- TODO when we're async
| _                        => throw (userError "got unsupported notification method")

partial def mainLoop : Unit → ServerM Unit
| () => do
  st ← read;
  msg ← readLspMessage st.hIn;
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

def mkLeanServerCapabilities : ServerCapabilities :=
{ textDocumentSync? := some
  { openClose := true,
    change := TextDocumentSyncKind.incremental,
    willSave := false,
    willSaveWaitUntil := false,
    save? := none },
  hoverProvider := true }

def initAndRunServerAux : ServerM Unit := do
st ← read;
_ ← readLspNotificationAs st.hIn "initialized" InitializedParams;
mainLoop ();
Message.notification "exit" none ← readLspMessage st.hIn
  | throw (userError "Expected an Exit Notification.");
pure ()

def initAndRunServer (i o : FS.Stream) : IO Unit := do
some workerPath ← IO.getEnv "LEAN_WORKER_PATH"
  | throw $ userError "You need to specify LEAN_WORKER_PATH in the environment.";
fileWorkersRef ← IO.mkRef (RBMap.empty : FileWorkerMap);
initRequest ← readLspRequestAs i "initialize" InitializeParams;
writeLspResponse o initRequest.id
  { capabilities := mkLeanServerCapabilities,
    serverInfo? := some { name := "Lean 4 server",
                          version? := "0.0.1" } : InitializeResult };
runReader
  initAndRunServerAux
  (⟨i, o, fileWorkersRef, initRequest.param, workerPath⟩ : ServerContext)

end Server
end Lean
