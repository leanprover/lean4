/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Init.System.IO
import Std.Data.RBMap

import Lean.Environment
import Lean.Server.Snapshots
import Lean.Server.Utils
import Lean.Data.Lsp
import Lean.Data.Json.FromToJson

/-!
For general server architecture, see `README.md`. For details of IPC communication, see `Watchdog.lean`.
This module implements per-file worker processes.

File processing and requests+notifications against a file should be concurrent for two reasons:
- By the LSP standard, requests should be cancellable.
- Since Lean allows arbitrary user code to be executed during elaboration via the tactic framework,
  elaboration can be extremely slow and even not halt in some cases. Users should be able to
  work with the file while this is happening, e.g. make new changes to the file or send requests.

To achieve these goals, elaboration is executed in a chain of tasks, where each task corresponds to
the elaboration of one command. When the elaboration of one command is done, the next task is spawned.
On didChange notifications, we search for the task in which the change occured. If we stumble across
a task that has not yet finished before finding the task we're looking for, we terminate it
and start the elaboration there, otherwise we start the elaboration at the task where the change occured.

Requests iterate over tasks until they find the command that they need to answer the request.
In order to not block the main thread, this is done in a request task.
If a task that the request task waits for is terminated, a change occured somewhere before the
command that the request is looking for and the request sends a "content changed" error.
-/

namespace Lean
namespace Server

open Lsp
open IO
open Snapshots

private def sendDiagnosticsCore (h : FS.Stream) (uri : DocumentUri) (version : Nat) (text : FileMap) (log : MessageLog)
  : IO Unit := do
diagnostics ← log.msgs.mapM (msgToDiagnostic text);
Lsp.writeLspNotification h "textDocument/publishDiagnostics"
  { uri := uri,
    version? := version,
    diagnostics := diagnostics.toArray : PublishDiagnosticsParams }

inductive TaskError
| aborted
| eof
| ioError (e : IO.Error)

inductive ElabTask
-- TODO(MH): Sebastian said something about wrapping next in Thunk but i did not have time to look into it yet
| mk (snap : Snapshot) (next : Task (Except TaskError ElabTask)) : ElabTask

namespace ElabTask

private def runTask (act : IO (Except TaskError ElabTask)) : IO (Task (Except TaskError ElabTask)) := do
t ← asTask act;
pure $ t.map $ fun error => match error with
| Except.ok e => e
| Except.error ioError => Except.error (TaskError.ioError ioError)

private partial def runCore (h : FS.Stream) (uri : DocumentUri) (version : Nat) (contents : FileMap) : Snapshot → IO (Except TaskError ElabTask)
| parent => do
  result ← compileNextCmd contents.source parent;
  match result with
  | Sum.inl snap => do
    -- TODO(MH): check for interrupt with increased precision
    canceled ← checkCanceled;
    if canceled then
      pure (Except.error TaskError.aborted)
    else do
      -- NOTE(MH): This relies on the client discarding old diagnostics upon receiving new ones
      -- while prefering newer versions over old ones. The former is necessary because we do
      -- not explicitly clear older diagnostics, while the latter is necessary because we do
      -- not guarantee that diagnostics are emitted in order. Specifically, it may happen that
      -- we interrupted this elaboration task right at this point and a newer elaboration task
      -- emits diagnostics, after which we emit old diagnostics because we did not yet detect
      -- the interrupt. Explicitly clearing diagnostics is difficult for a similar reason,
      -- because we cannot guarantee that no further diagnostics are emitted after clearing
      -- them.
      sendDiagnosticsCore h uri version contents snap.msgLog;
      t ← runTask (runCore snap);
      pure (Except.ok ⟨snap, t⟩)
  | Sum.inr msgLog => do
    canceled ← checkCanceled;
    if canceled then
      pure (Except.error TaskError.aborted)
    else do
      sendDiagnosticsCore h uri version contents msgLog;
      pure (Except.error TaskError.eof)

def run (h : FS.Stream) (uri : DocumentUri) (version : Nat) (contents : FileMap) (parent : Snapshot) : IO ElabTask := do
t ← runTask (runCore h uri version contents parent);
pure ⟨parent, t⟩

partial def branchOffAt (h : FS.Stream) (uri : DocumentUri) (version : Nat) (contents : FileMap) : ElabTask → String.Pos → IO ElabTask
| ⟨snap, nextTask⟩, changePos => do
  finished ← hasFinished nextTask;
  if finished then
    match nextTask.get with
    | Except.ok (next@⟨nextSnap, _⟩) =>
       -- if next contains the change ...
       -- (it will never be the header snap because the
       -- watchdog will never send didChange notifs with
       -- header changes to the file worker)
       if changePos < nextSnap.endPos then do
         newNext ← run h uri version contents snap;
         -- we do not need to cancel the old task explicitly since tasks without refs are marked as cancelled by the GC
         pure newNext
       else do
         newNext ← branchOffAt next changePos;
         pure ⟨snap, Task.pure (Except.ok newNext)⟩
    | Except.error e => match e with
      -- this case should not be possible. only the main task aborts tasks and ensures that aborted tasks
      -- do not show up in `snapshots` of EditableDocument below.
      | TaskError.aborted => throw (userError "reached case that should not be possible during server file worker task branching")
      | TaskError.eof => do
        newNext ← run h uri version contents snap;
        pure newNext
      | TaskError.ioError ioError => throw ioError
  else do
    newNext ← run h uri version contents snap;
    -- we do not need to cancel the old task explicitly since tasks without refs are marked as cancelled by the GC
    pure newNext

end ElabTask

/-- A document editable in the sense that we track the environment
and parser state after each command so that edits can be applied
without recompiling code appearing earlier in the file. -/
structure EditableDocument :=
(version : Nat)
(text : FileMap)
/- Subsequent snapshots occur after each command. -/
(snapshots : ElabTask)

namespace EditableDocument

open Elab

/-- Compiles the contents of a Lean file. -/
def compileDocument (h : FS.Stream) (uri : DocumentUri) (version : Nat) (text : FileMap) : IO EditableDocument := do
headerSnap ← Snapshots.compileHeader text.source;
task ← ElabTask.run h uri version text headerSnap;
let docOut : EditableDocument := ⟨version, text, task⟩;
pure docOut

/-- Given `changePos`, the UTF-8 offset of a change into the pre-change source,
and the new document, updates editable doc state. -/
def updateDocument (h : FS.Stream) (uri : DocumentUri) (doc : EditableDocument) (changePos : String.Pos) (newVersion : Nat) (newText : FileMap) : IO EditableDocument := do
newSnapshots ← doc.snapshots.branchOffAt h uri newVersion newText changePos;
pure ⟨newVersion, newText, newSnapshots⟩

end EditableDocument

open EditableDocument

open IO
open Std (RBMap RBMap.empty)
open JsonRpc

abbrev PendingRequestMap := RBMap RequestID (Task (Except IO.Error Unit)) (fun a b => Decidable.decide (a < b))

structure ServerContext :=
(hIn hOut : FS.Stream)
(docRef : IO.Ref EditableDocument)
(pendingRequestsRef : IO.Ref PendingRequestMap)

abbrev ServerM := ReaderT ServerContext IO

def setDocument (val : EditableDocument) : ServerM Unit :=
fun st => st.docRef.set val

def getDocument : ServerM EditableDocument :=
fun st => st.docRef.get

def updatePendingRequests (map : PendingRequestMap → PendingRequestMap) : ServerM Unit :=
fun st => st.pendingRequestsRef.modify map

/-- Clears diagnostics for the document version 'version'. -/
-- TODO(WN): how to clear all diagnostics? Sending version 'none' doesn't seem to work
def clearDiagnostics (uri : DocumentUri) (version : Nat) : ServerM Unit :=
fun st =>
writeLspNotification st.hOut "textDocument/publishDiagnostics"
  { uri := uri,
    version? := version,
    diagnostics := #[] : PublishDiagnosticsParams }

def sendDiagnostics (uri : DocumentUri) (doc : EditableDocument) (log : MessageLog)
  : ServerM Unit := do
fun st => monadLift $ sendDiagnosticsCore st.hOut uri doc.version doc.text log

def openDocument (h : FS.Stream) (p : DidOpenTextDocumentParams) : IO EditableDocument := do
let doc := p.textDocument;
-- NOTE(WN): `toFileMap` marks line beginnings as immediately following
-- "\n", which should be enough to handle both LF and CRLF correctly.
-- This is because LSP always refers to characters by (line, column),
-- so if we get the line number correct it shouldn't matter that there
-- is a CR there.
let text := doc.text.toFileMap;
newDoc ← compileDocument h doc.uri doc.version text;
pure newDoc

def handleDidChange (p : DidChangeTextDocumentParams) : ServerM Unit := do
let docId := p.textDocument;
let changes := p.contentChanges;
oldDoc ← getDocument;
some newVersion ← pure docId.version? | throw (userError "expected version number");
if newVersion <= oldDoc.version then do
  throw (userError "got outdated version number")
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
  st ← read;
  newDoc ← monadLift $
    updateDocument st.hOut docId.uri oldDoc minStartOff newVersion newDocText;
  setDocument newDoc

def handleCancelRequest (p : CancelParams) : ServerM Unit := do
updatePendingRequests (fun pendingRequests => pendingRequests.erase p.id)

-- TODO(MH): requests that need data from a certain command should traverse e.snapshots
-- by successively getting the next task, meaning that we might need to wait for elaboration.
-- Sebastian said something about a future function TaskIO.bind that ensures that the
-- request task will also stop waiting when the reference to the task is released by handleDidChange.
-- when that happens, the request should send a "content changed" error to the user.
-- (this way, the server doesn't get bogged down in requests for an old state of the document)
-- requests need to manually check for whether their task has been cancelled, so that they
-- can reply with a RequestCancelled error.
def handleHover (p : HoverParams) (e : EditableDocument) : IO Unit := pure ⟨⟩

def parseParams (paramType : Type*) [HasFromJson paramType] (params : Json) : ServerM paramType :=
match fromJson? params with
| some parsed => pure parsed
| none        => throw (userError "got param with wrong structure")

def handleNotification (method : String) (params : Json) : ServerM Unit := do
let h := (fun paramType [HasFromJson paramType] (handler : paramType → ServerM Unit) =>
  parseParams paramType params >>= handler);
match method with
| "textDocument/didChange" => h DidChangeTextDocumentParams handleDidChange
| "$/cancelRequest"        => pure () -- TODO when we're async
| _                        => throw (userError ("got unsupported notification method: " ++ method))

def queueRequest {α : Type*} (id : RequestID) (handler : α → EditableDocument → IO Unit) (params : α) : ServerM Unit := do
doc ← getDocument;
requestTask ← monadLift $ asTask (handler params doc);
updatePendingRequests (fun pendingRequests => pendingRequests.insert id requestTask)

def handleRequest (id : RequestID) (method : String) (params : Json)
  : ServerM Unit := do
let h := (fun paramType [HasFromJson paramType]
              (handler : paramType → EditableDocument → IO Unit) =>
           parseParams paramType params >>= queueRequest id handler);
match method with
| "textDocument/hover" => h HoverParams handleHover
| _ => throw (userError $ "got unsupported request: " ++ method ++
                          "; params: " ++ toString params)

partial def mainLoop : Unit → ServerM Unit
| () => do
  st ← read;
  msg ← readLspMessage st.hIn;
  pendingRequests ← st.pendingRequestsRef.get;
  let filterFinishedTasks : PendingRequestMap → RequestID → Task (Except IO.Error Unit) → IO PendingRequestMap := 
    (fun acc id task => do
      f ← hasFinished task;
      pure $ if f then
        acc.erase id
      else
        acc);
  pendingRequests ← monadLift $ pendingRequests.foldM filterFinishedTasks pendingRequests;
  st.pendingRequestsRef.set pendingRequests;
  match msg with
  | Message.request id method (some params) => do
    handleRequest id method (toJson params);
    mainLoop ()
  | Message.notification "exit" none => do
    -- should be sufficient to shut down the file worker.
    -- references are lost => tasks are marked as cancelled
    -- => all tasks eventually quit
    pure ()
  | Message.notification method (some params) => do
    handleNotification method (toJson params);
    mainLoop ()
  | _ => throw (userError "got invalid JSON-RPC message")

def initAndRunWorker (i o : FS.Stream) : IO Unit := do
-- TODO(WN): act in accordance with InitializeParams
_ ← Lsp.readLspRequestAs i "initialize" InitializeParams;
param ← Lsp.readLspNotificationAs i "textDocument/didOpen" DidOpenTextDocumentParams;
doc ← openDocument o param;
docRef ← IO.mkRef doc;
pendingRequestsRef ← IO.mkRef (RBMap.empty : PendingRequestMap);
runReader (mainLoop ()) (⟨i, o, docRef, pendingRequestsRef⟩ : ServerContext)

end Server
end Lean

def main (_ : List String) : IO UInt32 := do
i ← IO.getStdin;
o ← IO.getStdout;
e ← IO.getStderr;
Lean.initSearchPath;
catch
  (Lean.Server.initAndRunWorker i o)
  (fun err => e.putStrLn (toString err));
pure 0
