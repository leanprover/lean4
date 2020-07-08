import Lean.Environment
import Lean.Elab.Frontend
import Lean.Data.Lsp
import Lean.Data.Json.FromToJson
import Init.System.IO

namespace Lean.Server

open IO
open Lean
open Lean.JsonRpc
open Lean.Lsp
open Lean.Elab

-- LSP indexes text with rows and colums
abbrev DocumentText := Array String

structure Document :=
(version : Int)
(text : DocumentText)
(headerEnv : Environment)

abbrev DocumentMap := RBMap DocumentUri Document (fun a b => Decidable.decide (a < b))

structure ServerState :=
(i o : FS.Handle)
(openDocumentsRef : IO.Ref DocumentMap)

def parseParams (paramType : Type*) [HasFromJson paramType] (params : Json) : IO paramType :=
match @fromJson? paramType _ params with
| some parsed => pure parsed
| none        => throw (userError "got param with wrong structure")

def runFrontend (text : String) : IO (Environment × Environment × MessageLog) := do
let inputCtx := Parser.mkInputContext text "<input>";
envNul ← mkEmptyEnvironment;
match Parser.parseHeader envNul inputCtx with
| (header, parserState, messages) => do
  (env, messages) ← processHeader header messages inputCtx;
  parserStateRef ← IO.mkRef parserState;
  cmdStateRef ← IO.mkRef $ Command.mkState env messages {};
  IO.processCommands inputCtx parserStateRef cmdStateRef;
  cmdState ← cmdStateRef.get;
  pure (env, cmdState.env, cmdState.messages)

def updateFrontend (env : Environment) (input : String) : IO (Environment × MessageLog) := do
let inputCtx := Parser.mkInputContext input "<input>";
parserStateRef ← IO.mkRef ({} : Parser.ModuleParserState);
cmdStateRef    ← IO.mkRef $ Command.mkState env;
IO.processCommands inputCtx parserStateRef cmdStateRef;
cmdState ← cmdStateRef.get;
pure (cmdState.env, cmdState.messages)

def msgToDiagnostic (text : DocumentText) (m : Lean.Message) : Diagnostic :=
-- Lean Message line numbers are 1-based while LSP Positions are 0-based.
let lowLn := m.pos.line - 1;
let low : Lsp.Position := ⟨lowLn, (text.get! lowLn).codepointPosToUtf16Pos m.pos.column⟩;
let high : Lsp.Position := match m.endPos with
| some endPos =>
  let highLn := endPos.line - 1;
  ⟨highLn, (text.get! highLn).codepointPosToUtf16Pos endPos.column⟩
| none        => low;
let range : Range := ⟨low, high⟩;
let severity := match m.severity with
| MessageSeverity.information => DiagnosticSeverity.information
| MessageSeverity.warning     => DiagnosticSeverity.warning
| MessageSeverity.error       => DiagnosticSeverity.error;
let source := "Lean 4 server";
let message := toString (format m.data);
{ range := range
, severity? := severity
, source? := source
, message := message}

namespace ServerState

def findOpenDocument (s : ServerState) (key : DocumentUri) : IO Document := do
openDocuments ← s.openDocumentsRef.get;
match openDocuments.find? key with
| some doc => pure doc
| none     => throw (userError "got unknown document uri")

def updateOpenDocuments (s : ServerState) (key : DocumentUri) (val : Document) : IO Unit :=
s.openDocumentsRef.modify (fun documents => (documents.erase key).insert key val)

-- Clears diagnostics for the document version 'd'.
-- TODO how to clear all diagnostics? Sending version 'none' doesn't seem to work
def clearDiagnostics (s : ServerState) (uri : DocumentUri) (d : Document) : IO Unit :=
writeLspNotification s.o "textDocument/publishDiagnostics"
  { uri := uri
  , version? := d.version
  , diagnostics := #[] : PublishDiagnosticsParams }

def sendDiagnostics (s : ServerState) (uri : DocumentUri) (d : Document) (log : MessageLog) : IO Unit :=
let diagnostics := log.msgs.map (msgToDiagnostic d.text);
writeLspNotification s.o "textDocument/publishDiagnostics"
  { uri := uri
  , version? := d.version
  , diagnostics := diagnostics.toArray : PublishDiagnosticsParams }

def handleDidOpen (s : ServerState) (p : DidOpenTextDocumentParams) : IO Unit := do
let doc := p.textDocument;
let text := doc.text.splitOnEOLs;
(headerEnv, env, msgLog) ← runFrontend ("\n".intercalate text);
let newDoc : Document := ⟨doc.version, text.toArray, headerEnv⟩;
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
    (newEnv, msgLog) ← updateFrontend oldDoc.headerEnv ("\n".intercalate newDocText.toList);
    let newDoc : Document := ⟨newVersion, newDocText, oldDoc.headerEnv⟩;
    s.updateOpenDocuments docId.uri newDoc;
    -- Clients don't have to clear diagnostics, so we clear them
    -- for the *previous* version here.
    s.clearDiagnostics docId.uri oldDoc;
    s.sendDiagnostics docId.uri newDoc msgLog

  | TextDocumentContentChangeEvent.fullChange (text : String) =>
    throw (userError "got content change that replaces the full document (not supported)")

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

def initialize (i o : FS.Handle) : IO Unit := do
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
catch (Lean.Server.initialize i o) (fun err => o.putStrLn (toString err));
pure 0
