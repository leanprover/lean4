/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Init.System.IO
import Std.Data.RBMap

import Lean.Environment
import Lean.Server.Snapshots
import Lean.Data.Lsp
import Lean.Data.Json.FromToJson

namespace Lean
namespace Server

open Lsp

/-- A document editable in the sense that we track the environment
and parser state after each command so that edits can be applied
without recompiling code appearing earlier in the file. -/
structure EditableDocument where
  version : Nat
  text : FileMap
  /- The first snapshot is that after the header. -/
  header : Snapshots.Snapshot
  /- Subsequent snapshots occur after each command. -/
  -- TODO(WN): These should probably be asynchronous Tasks
  snapshots : List Snapshots.Snapshot

namespace EditableDocument

open Elab

/-- Compiles the contents of a Lean file. -/
def compileDocument (version : Nat) (text : FileMap) : IO (MessageLog × EditableDocument) := do
  let headerSnap ← Snapshots.compileHeader text.source
  let (cmdSnaps, msgLog) ← Snapshots.compileCmdsAfter text.source headerSnap
  let docOut : EditableDocument := ⟨version, text, headerSnap, cmdSnaps⟩
  pure (msgLog, docOut)

/-- Given `changePos`, the UTF-8 offset of a change into the pre-change source,
and the new document, updates editable doc state. -/
def updateDocument (doc : EditableDocument) (changePos : String.Pos) (newVersion : Nat) (newText : FileMap) : IO (MessageLog × EditableDocument) := do
  let recompileEverything := do
    -- TODO free compacted regions
    compileDocument newVersion newText
  /- If the change occurred before the first command
  or there are no commands yet, recompile everything. -/
  match doc.snapshots.head? with
  | none => recompileEverything
  | some firstSnap =>
    if firstSnap.beginPos > changePos then
      recompileEverything
    else
      -- NOTE(WN): endPos is greedy in that it consumes input until the next token,
      -- so a change on some whitespace after a command recompiles it. We could
      -- be more precise.
      let validSnaps := doc.snapshots.filter (fun snap => snap.endPos < changePos)
      -- The lowest-in-the-file snapshot which is still valid.
      let lastSnap := validSnaps.getLastD doc.header
      let (snaps, msgLog) ← Snapshots.compileCmdsAfter newText.source lastSnap
      let newDoc := { version := newVersion,
                      header := doc.header,
                      text := newText,
                      snapshots := validSnaps ++ snaps : EditableDocument }
      pure (msgLog, newDoc)

end EditableDocument

open EditableDocument

open IO
open Std (RBMap RBMap.empty)
open JsonRpc

abbrev DocumentMap :=
  RBMap DocumentUri EditableDocument (fun a b => Decidable.decide (a < b))

structure ServerContext where
  hIn hOut : FS.Stream
  openDocumentsRef : IO.Ref DocumentMap
  -- TODO (requestsInFlight : IO.Ref (Array (Task (Σ α, Response α))))

abbrev ServerM := ReaderT ServerContext IO

def findOpenDocument (key : DocumentUri) : ServerM EditableDocument := fun st => do
  let openDocuments ← st.openDocumentsRef.get;
  match openDocuments.find? key with
  | some doc => pure doc
  | none     => throw (userError $ "got unknown document URI (" ++ key ++ ")")

def updateOpenDocuments (key : DocumentUri) (val : EditableDocument) : ServerM Unit := fun st =>
  st.openDocumentsRef.modify (fun documents => documents.insert key val)

def readLspMessage : ServerM JsonRpc.Message := fun st =>
  Lsp.readLspMessage st.hIn

def readLspRequestAs (expectedMethod : String) (α : Type) [FromJson α] : ServerM (Request α) := fun st =>
  Lsp.readLspRequestAs st.hIn expectedMethod α

def readLspNotificationAs (expectedMethod : String) (α : Type) [FromJson α] : ServerM α := fun st =>
  Lsp.readLspNotificationAs st.hIn expectedMethod α

def writeLspNotification {α : Type} [ToJson α] (method : String) (params : α) : ServerM Unit := fun st =>
  Lsp.writeLspNotification st.hOut method params

def writeLspResponse {α : Type} [ToJson α] (id : RequestID) (params : α) : ServerM Unit := fun st =>
  Lsp.writeLspResponse st.hOut id params

/-- Clears diagnostics for the document version 'version'. -/
-- TODO(WN): how to clear all diagnostics? Sending version 'none' doesn't seem to work
def clearDiagnostics (uri : DocumentUri) (version : Nat) : ServerM Unit :=
  writeLspNotification "textDocument/publishDiagnostics"
    { uri := uri,
      version? := version,
      diagnostics := #[] : PublishDiagnosticsParams }

def sendDiagnostics (uri : DocumentUri) (doc : EditableDocument) (log : MessageLog) : ServerM Unit := do
  let diagnostics ← log.msgs.mapM fun msg => liftM $ msgToDiagnostic doc.text msg
  writeLspNotification "textDocument/publishDiagnostics"
    { uri := uri,
      version? := doc.version,
      diagnostics := diagnostics.toArray : PublishDiagnosticsParams }

def handleDidOpen (p : DidOpenTextDocumentParams) : ServerM Unit := do
  let doc := p.textDocument
  -- NOTE(WN): `toFileMap` marks line beginnings as immediately following
  -- "\n", which should be enough to handle both LF and CRLF correctly.
  -- This is because LSP always refers to characters by (line, column),
  -- so if we get the line number correct it shouldn't matter that there
  -- is a CR there.
  let text := doc.text.toFileMap
  let (msgLog, newDoc) ← compileDocument doc.version text
  updateOpenDocuments doc.uri newDoc
  sendDiagnostics doc.uri newDoc msgLog

private def replaceLspRange (text : FileMap) (r : Lsp.Range) (newText : String) : FileMap :=
  let start := text.lspPosToUtf8Pos r.start;
  let «end» := text.lspPosToUtf8Pos r.«end»;
  let pre := text.source.extract 0 start;
  let post := text.source.extract «end» text.source.bsize;
  (pre ++ newText ++ post).toFileMap

def handleDidChange (p : DidChangeTextDocumentParams) : ServerM Unit := do
  let docId := p.textDocument
  let changes := p.contentChanges
  let oldDoc ← findOpenDocument docId.uri
  let some newVersion ← pure docId.version? | throw (userError "expected version number")
  if newVersion <= oldDoc.version then do
    throw (userError "got outdated version number")
  else changes.forM fun change =>
    match change with
    | TextDocumentContentChangeEvent.rangeChange (range : Range) (newText : String) => do
      let startOff := oldDoc.text.lspPosToUtf8Pos range.start
      let newDocText := replaceLspRange oldDoc.text range newText
      let (msgLog, newDoc) ← monadLift $
        updateDocument oldDoc startOff newVersion newDocText
      updateOpenDocuments docId.uri newDoc
      -- Clients don't have to clear diagnostics, so we clear them
      -- for the *previous* version here.
      clearDiagnostics docId.uri oldDoc.version
      sendDiagnostics docId.uri newDoc msgLog

    | TextDocumentContentChangeEvent.fullChange (text : String) =>
      throw (userError "TODO impl computing the diff of two sources.")

def handleDidClose (p : DidCloseTextDocumentParams) : ServerM Unit := fun st => do
  -- TODO free compacted regions
  st.openDocumentsRef.modify (fun openDocuments => openDocuments.erase p.textDocument.uri)

def handleHover (p : HoverParams) : ServerM Json := pure Json.null

def parseParams (paramType : Type) [FromJson paramType] (params : Json) : ServerM paramType :=
  match fromJson? params with
  | some parsed => pure parsed
  | none        => throw (userError "got param with wrong structure")

def handleNotification (method : String) (params : Json) : ServerM Unit := do
  let h := (fun paramType [FromJson paramType] (handler : paramType → ServerM Unit) =>
    parseParams paramType params >>= handler)
  match method with
  | "textDocument/didOpen"   => h DidOpenTextDocumentParams handleDidOpen
  | "textDocument/didChange" => h DidChangeTextDocumentParams handleDidChange
  | "textDocument/didClose"  => h DidCloseTextDocumentParams handleDidClose
  | "$/cancelRequest"        => pure () -- TODO when we're async
  | _                        => throw (userError "got unsupported notification method")

def handleRequest (id : RequestID) (method : String) (params : Json) : ServerM Unit := do
  let h := (fun paramType responseType [FromJson paramType] [ToJson responseType]
                (handler : paramType → ServerM responseType) =>
             parseParams paramType params >>= handler >>= writeLspResponse id)
  match method with
  | "textDocument/hover" => h HoverParams Json handleHover
  | _ => throw (userError $ "got unsupported request: " ++ method ++
                            "; params: " ++ toString params)

partial def mainLoop (_ : Unit) : ServerM Unit := do
  let msg ← readLspMessage
  match msg with
  | Message.request id "shutdown" _ =>
    writeLspResponse id (Json.null)
  | Message.request id method (some params) => do
    handleRequest id method (toJson params);
    mainLoop ()
  | Message.notification method (some params) => do
    handleNotification method (toJson params);
    mainLoop ()
  | _ => throw (userError "got invalid JSON-RPC message")

def mkLeanServerCapabilities : ServerCapabilities := {
  textDocumentSync? := some {
    openClose := true,
    change := TextDocumentSyncKind.incremental,
    willSave := false,
    willSaveWaitUntil := false,
    save? := none
  },
  hoverProvider := true
}

def initAndRunServer (i o : FS.Stream) : IO Unit := do
  let openDocumentsRef ← IO.mkRef (RBMap.empty : DocumentMap)
  let x : ServerM Unit := do
    -- ignore InitializeParams for MWE
    let r ← readLspRequestAs "initialize" InitializeParams
    writeLspResponse r.id
      { capabilities := mkLeanServerCapabilities,
        serverInfo? := some { name := "Lean 4 server",
                              version? := "0.0.1" } : InitializeResult }
    readLspNotificationAs "initialized" InitializedParams
    mainLoop ()
    let Message.notification "exit" none ← readLspMessage
      | throw (userError "Expected an Exit Notification.")
  x.run ⟨i, o, openDocumentsRef⟩

namespace Test

def runWithInputFile (fn : String) (searchPath : Option String) : IO Unit := do
let o ← IO.getStdout
let e ← IO.getStderr
FS.withFile fn FS.Mode.read fun hFile => do
  Lean.initSearchPath searchPath
  try
    Lean.Server.initAndRunServer (FS.Stream.ofHandle hFile) o
  catch err =>
    e.putStrLn (toString err)

end Test
end Server
end Lean
