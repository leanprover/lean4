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

structure Document := (version : Int) (text : DocumentText) (env : Environment)

abbrev DocumentMap := RBMap DocumentUri Document (fun a b => Decidable.decide (a < b))

structure ServerState :=
(i o : FS.Handle)
(openDocumentsRef : IO.Ref DocumentMap)

def parseParams (paramType : Type*) [HasFromJson paramType] (params : Json) : IO paramType :=
match @fromJson? paramType _ params with
| some parsed => pure parsed
| none        => throw (userError "got param with wrong structure")

def updateFrontend (env : Environment) (input : String) : IO (Environment × MessageLog) := do
let inputCtx := Parser.mkInputContext input "<input>";
parserStateRef ← IO.mkRef ({} : Parser.ModuleParserState);
cmdStateRef    ← IO.mkRef $ Command.mkState env;
IO.processCommands inputCtx parserStateRef cmdStateRef;
cmdState ← cmdStateRef.get;
pure (cmdState.env, cmdState.messages)

def msgToDiagnostic (text : DocumentText) (m : Lean.Message) : Diagnostic :=
let low : Lsp.Position := ⟨m.pos.line, (text.get! m.pos.line).codepointPosToUtf16Pos m.pos.column⟩;
let high : Lsp.Position := match m.endPos with
| some endPos => ⟨endPos.line, (text.get! endPos.line).codepointPosToUtf16Pos endPos.column⟩
| none        => low;
let range : Range := ⟨low, high⟩;
let severity := match m.severity with
| MessageSeverity.information => DiagnosticSeverity.information
| MessageSeverity.warning     => DiagnosticSeverity.warning
| MessageSeverity.error       => DiagnosticSeverity.error;
let source := "Lean 4 server";
let message := toString (format m.data);
{range := range, severity? := severity, source? := source, message := message}

namespace ServerState

def findOpenDocument (s : ServerState) (key : DocumentUri) : IO Document := do
openDocuments ← s.openDocumentsRef.get;
match openDocuments.find? key with
| some doc => pure doc
| none     => throw (userError "got unknown document uri")

def updateOpenDocuments (s : ServerState) (key : DocumentUri) (val : Document) : IO Unit :=
s.openDocumentsRef.modify (fun documents => (documents.erase key).insert key val)

def sendDiagnostics (s : ServerState) (uri : DocumentUri) (d : Document) (log : MessageLog) : IO Unit := 
let diagnostics := log.msgs.map (msgToDiagnostic d.text);
writeLspNotification s.o "textDocument/publishDiagnostics" {PublishDiagnosticsParams . uri := uri, version? := d.version, diagnostics := diagnostics.toArray}

def handleDidOpen (s : ServerState) (p : DidOpenTextDocumentParams) : IO Unit := do
let d := p.textDocument;
let text := d.text.splitOnEOLs;
(env, msgLog) ← runFrontend {const2ModIdx := {}, constants := {}, extensions := #[]} ("\n".intercalate text);
let newDoc : Document := ⟨d.version, text.toArray, env⟩;
s.openDocumentsRef.modify (fun openDocuments => openDocuments.insert d.uri newDoc);
s.sendDiagnostics d.uri newDoc msgLog

def handleDidChange (s : ServerState) (p : DidChangeTextDocumentParams) : IO Unit := do
let d := p.textDocument;
let c := p.contentChanges;
oldDoc ← s.findOpenDocument d.uri;
some newVersion ← pure d.version? | throw (userError "expected version number");
if newVersion <= oldDoc.version then do
  throw (userError "got outdated version number")
else c.forM $ fun change =>
  match change with
  | TextDocumentContentChangeEvent.rangeChange (range : Range) (newText : String) => do
    let newDocText := replaceRange oldDoc.text range newText;
    -- (newEnv, newMsgLog) ← updateFrontend oldDoc.env ("\n".intercalate newDocText.toList);
    (newEnv, msgLog) ← runFrontend {const2ModIdx := {}, constants := {}, extensions := #[]} ("\n".intercalate newDocText.toList);
    let newDoc : Document := ⟨newVersion, newDocText, newEnv⟩;
    s.updateOpenDocuments d.uri newDoc;
    s.sendDiagnostics d.uri newDoc msgLog
  | TextDocumentContentChangeEvent.fullChange (text : String) => throw (userError "got content change that replaces the full document (not supported)") 

def handleNotification (s : ServerState) (method : String) (params : Json) : IO Unit := do
let h := (fun paramType [HasFromJson paramType] (handler : ServerState → paramType → IO Unit) => 
  parseParams paramType params >>= handler s);
match method with
| "textDocument/didOpen"   => h DidOpenTextDocumentParams handleDidOpen
| "textDocument/didChange" => h DidChangeTextDocumentParams handleDidChange
| _                        => throw (userError "got unsupported notification method")

partial def mainLoop : ServerState → IO Unit
| s => do
  m ← readLspMessage s.i;
  match m with
  | Message.request id method (some params) => pure ()
  | Message.requestNotification method (some params) => do
    s.handleNotification method (toJson params);
    mainLoop s
  | _ => throw (userError "got invalid jsonrpc message")

end ServerState

def initialize (i o : FS.Handle) : IO Unit := do
-- ignore InitializeParams for MWE
r ← readLspRequestAs i "initialize" InitializeParams;
writeLspResponse o r.id mkLeanServerCapabilities;
_ ← readLspRequestNotificationAs i "initialized" Initialized;
openDocumentsRef ← IO.mkRef (RBMap.empty : DocumentMap);
ServerState.mainLoop ⟨i, o, openDocumentsRef⟩

end Lean.Server

def main (n : List String) : IO UInt32 := do
i ← IO.stdin;
o ← IO.stdout;
catch (Lean.Server.initialize i o) (fun err => o.putStrLn (toString err));
pure 0
