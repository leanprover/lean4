import Init.System.IO
import Std.Data.RBMap

import Lean.Environment
import Lean.Server.Snapshots
import Lean.Data.Lsp
import Lean.Data.Json.FromToJson

namespace Lean.Server
namespace Editable

open Lean.Lsp
open Lean.Elab

/-- A document editable in the sense that we track the environment
and parser state after each command so that edits can be applied
without recompiling code appearing earlier in the file. -/
structure EditableDocument :=
(version : Nat)
(text : DocumentText)
/- The first snapshot is that after the header. -/
(header : Snapshots.Snapshot)
/- Subsequent snapshots occur after each command. -/
-- TODO(WN): These should probably be asynchronous Tasks
(snapshots : List Snapshots.Snapshot)

/-- Compiles the contents of a Lean file. -/
def compileDocument (version : Nat) (text : DocumentText)
  : IO (Lean.MessageLog × EditableDocument) := do
let contents := "\n".intercalate text.toList;
headerSnap ← Snapshots.compileHeader contents;
cmdSnaps ← Snapshots.compileCmdsAfter contents headerSnap;
let docOut : EditableDocument := ⟨version, text, headerSnap, cmdSnaps⟩;
let msgLog := (cmdSnaps.getLastD headerSnap).msgLog;
pure (msgLog, docOut)

def updateDocument (doc : EditableDocument) (changePos : Position) (newVersion : Nat)
  (newText : DocumentText) : IO (Lean.MessageLog × EditableDocument) := do
let newContents := "\n".intercalate newText.toList;
let changePos := doc.text.lnColToLinearPos changePos;
let recompileEverything := compileDocument newVersion newText;
/- If the change occurred before the first command
or there are no commands yet, recompile everything. -/
match doc.snapshots.head? with
| none => recompileEverything
| some firstSnap =>
  if firstSnap.beginPos > changePos then
    recompileEverything
  else do
    let validSnaps := doc.snapshots.filter (fun snap => snap.endPos < changePos);
    -- The lowest-in-the-file snapshot which is still valid;
    -- TODO(WN): endPos is greedy in that it consumes input until the next token,
    -- so a change on some whitespace after a command recompiles it. We could
    -- be more precise.
    let lastSnap := validSnaps.getLastD doc.header;
    snaps ← Snapshots.compileCmdsAfter newContents lastSnap;
    let newDoc := { version := newVersion
                  , header := doc.header
                  , text := newText
                  , snapshots := validSnaps ++ snaps : EditableDocument };
    let msgLog := (newDoc.snapshots.getLastD newDoc.header).msgLog;
    pure (msgLog, newDoc)

end Editable

open Editable

open IO
open Std (RBMap RBMap.empty)
open Lean
open Lean.JsonRpc
open Lean.Lsp
open Lean.Elab

abbrev DocumentMap :=
  RBMap DocumentUri EditableDocument (fun a b => Decidable.decide (a < b))

structure ServerState :=
(i o : FS.Handle)
(openDocumentsRef : IO.Ref DocumentMap)

def parseParams (paramType : Type*) [HasFromJson paramType] (params : Json) : IO paramType :=
match @fromJson? paramType _ params with
| some parsed => pure parsed
| none        => throw (userError "got param with wrong structure")

-- def ServerM α := StateT ServerState (IO α)
-- Computes a task with result type α in the ServerM monad.
-- def ServerTaskM α := ServerM (Task α)
-- Handles a request with params of type α and response params β.
-- def RequestHandler α β := Request α → ServerTaskM (Response β)

namespace ServerState

def findOpenDocument (s : ServerState) (key : DocumentUri) : IO EditableDocument := do
openDocuments ← s.openDocumentsRef.get;
match openDocuments.find? key with
| some doc => pure doc
| none     => throw (userError "got unknown document uri")

def updateOpenDocuments (s : ServerState) (key : DocumentUri) (val : EditableDocument) : IO Unit :=
s.openDocumentsRef.modify (fun documents => (documents.erase key).insert key val)

-- Clears diagnostics for the document version 'version'.
-- TODO how to clear all diagnostics? Sending version 'none' doesn't seem to work
-- TODO arg should be versioneddocumentidentifier
def clearDiagnostics (s : ServerState) (uri : DocumentUri) (version : Nat) : IO Unit :=
writeLspNotification s.o "textDocument/publishDiagnostics"
  { uri := uri
  , version? := version
  , diagnostics := #[] : PublishDiagnosticsParams }

def sendDiagnostics (s : ServerState) (uri : DocumentUri) (doc : EditableDocument)
  (log : MessageLog) : IO Unit :=
let diagnostics := log.msgs.map (msgToDiagnostic doc.text);
writeLspNotification s.o "textDocument/publishDiagnostics"
  { uri := uri
  , version? := doc.version
  , diagnostics := diagnostics.toArray : PublishDiagnosticsParams }

def handleDidOpen (s : ServerState) (p : DidOpenTextDocumentParams) : IO Unit := do
let doc := p.textDocument;
-- The text being split here is going to be immediately
-- intercalated with '\n' but this is useful to get rid of
-- CRLFs.
let text := doc.text.splitOnEOLs.toArray;
(msgLog, newDoc) ← compileDocument doc.version text;
s.openDocumentsRef.modify (fun openDocuments => openDocuments.insert doc.uri newDoc);
s.sendDiagnostics doc.uri newDoc msgLog

def handleDidChange (s : ServerState) (p : DidChangeTextDocumentParams) : IO Unit := do
let docId := p.textDocument;
let changes := p.contentChanges;
oldDoc ← s.findOpenDocument docId.uri;
some newVersion ← pure docId.version? | throw (userError "expected version number");
if newVersion <= oldDoc.version then do
  throw (userError "got outdated version number")
else changes.forM $ fun change =>
  match change with
  | TextDocumentContentChangeEvent.rangeChange (range : Range) (newText : String) => do
    let newDocText := replaceRange oldDoc.text range newText;
    -- TODO(WN): turn range.start from utf16 into a codepoint pos
    (msgLog, newDoc) ← updateDocument oldDoc range.start newVersion newDocText;
    s.updateOpenDocuments docId.uri newDoc;
    -- Clients don't have to clear diagnostics, so we clear them
    -- for the *previous* version here.
    s.clearDiagnostics docId.uri oldDoc.version;
    s.sendDiagnostics docId.uri newDoc msgLog

  | TextDocumentContentChangeEvent.fullChange (text : String) =>
    throw (userError "TODO impl computing the diff of two sources.")

def handleDidClose (s : ServerState) (p : DidCloseTextDocumentParams) : IO Unit := do
-- TODO is any extra cleanup needed?
s.openDocumentsRef.modify (fun openDocuments => openDocuments.erase p.textDocument.uri)

def handleNotification (s : ServerState) (method : String) (params : Json) : IO Unit := do
let h := (fun paramType [HasFromJson paramType] (handler : ServerState → paramType → IO Unit) =>
  parseParams paramType params >>= handler s);
match method with
| "textDocument/didOpen"   => h DidOpenTextDocumentParams handleDidOpen
| "textDocument/didChange" => h DidChangeTextDocumentParams handleDidChange
| "textDocument/didClose"  => h DidCloseTextDocumentParams handleDidClose
| _                        => throw (userError "got unsupported notification method")

def handleRequest (s : ServerState) (id : RequestID) (method : String) (params : Json)
  : IO Unit := do
  match method with
  | "textDocument/hover" => do
    p ← parseParams HoverParams params;
    writeLspResponse s.o id Json.null;
    pure ()
  | _ => throw (userError "Not supporting requests for now!")

partial def mainLoop : ServerState → IO Unit
| s => do
  m ← readLspMessage s.i;
  match m with
  | Message.request id method (some params) => do
    s.handleRequest id method (toJson params);
    mainLoop s
  | Message.request id "shutdown" none =>
    writeLspResponse s.o id (Json.null)
  | Message.requestNotification method (some params) => do
    s.handleNotification method (toJson params);
    mainLoop s
  | _ => throw (userError "got invalid jsonrpc message")

end ServerState

def initAndRunServer (i o : FS.Handle) : IO Unit := do
-- ignore InitializeParams for MWE
r ← readLspRequestAs i "initialize" InitializeParams;
writeLspResponse o r.id ({ capabilities := mkLeanServerCapabilities
                         , serverInfo? := some { name := "Lean 4 server"
                                               , version? := "0.0.1" }} : InitializeResult);
_ ← readLspRequestNotificationAs i "initialized" Initialized;
openDocumentsRef ← IO.mkRef (RBMap.empty : DocumentMap);
ServerState.mainLoop ⟨i, o, openDocumentsRef⟩;
Message.requestNotification "exit" none ← readLspMessage i
  | throw (userError "Expected an Exit Notification.");
pure ()

end Lean.Server

def main (n : List String) : IO UInt32 := do
i ← IO.stdin;
o ← IO.stdout;
e ← IO.stderr;
Lean.initSearchPath;
env ← Lean.mkEmptyEnvironment;
catch (Lean.Server.initAndRunServer i o) (fun err => e.putStrLn (toString err));
pure 0
