import Lean.Data.Json
import Lean.Data.Lsp.Structure

namespace Lean.Lsp

open Lean
open Lean.Json

inductive TextDocumentSyncKind
/- Documents should not be synced at all. -/
--| none
/- Documents are synced by always sending the full content of the document. -/
| full
/- Documents are synced by sending the full content on open. After that only incremental updates to the document are send. -/
| incremental

structure TextDocumentSyncOptions :=
/- Open and close notifications are sent to the server.
If omitted open close notification should not be sent. -/
(openClose : Bool)
/- Change notifications are sent to the server.
If omitted it defaults to TextDocumentSyncKind.None.
none: not synced -/
(change? : Option TextDocumentSyncKind := none)

structure DidOpenTextDocumentParams :=
(textDocument : TextDocumentItem)

instance didOpenTextDocumentParamsHasFromJson : HasFromJson DidOpenTextDocumentParams :=
⟨fun j => do
  textDocument ← j.getObjValAs? TextDocumentItem "textDocument";
  pure ⟨textDocument⟩⟩

structure TextDocumentChangeRegistrationOptions :=
(documentSelector? : Option DocumentSelector := none)
(syncKind : TextDocumentSyncKind)

inductive TextDocumentContentChangeEvent
-- omitted: deprecated rangeLength
| rangeChange (range : Range) (text : String)
| fullChange (text : String)

structure DidChangeTextDocumentParams :=
-- version number points to version after all changes have been applied
(textDocument : VersionedTextDocumentIdentifier)
(contentChanges : Array TextDocumentContentChangeEvent)

-- TODO: missing:
-- WillSaveTextDocumentParams, TextDocumentSaveReason, SaveOptions
-- TextDocumentSaveRegistrationOptions, DidSaveTextDocumentParams

structure DidCloseTextDocumentParams := (textDocument : TextDocumentIdentifier)

instance textDocumentSyncKindHasFromJson : HasFromJson TextDocumentSyncKind :=
⟨fun j => match j.getNat? with
  | some 1 => TextDocumentSyncKind.full
  | some 2 => TextDocumentSyncKind.incremental
  | _      => none⟩

instance textDocumentSyncKindHasToJson : HasToJson TextDocumentSyncKind :=
⟨fun o => match o with
  | TextDocumentSyncKind.full => (1 : Nat)
  | TextDocumentSyncKind.incremental => (2 : Nat)⟩

instance textDocumentSyncOptionsHasFromJson : HasFromJson TextDocumentSyncOptions :=
⟨fun j => do
  openClose ← j.getObjValAs? Bool "openClose";
  let change? := j.getObjValAs? TextDocumentSyncKind "change";
  pure ⟨openClose, change?⟩⟩

instance textDocumentSyncOptionsHasToJson : HasToJson TextDocumentSyncOptions :=
⟨fun o => mkObj $
  ⟨"openClose", o.openClose⟩ :: opt "change" o.change? ++ []⟩

instance textDocumentChangeRegistrationOptionsHasFromJson : HasFromJson TextDocumentChangeRegistrationOptions :=
⟨fun j => do
  let documentSelector? := j.getObjValAs? DocumentSelector "documentSelector";
  syncKind ← j.getObjValAs? TextDocumentSyncKind "syncKind";
  pure ⟨documentSelector?, syncKind⟩⟩

instance textDocumentContentChangeEventHasFromJson : HasFromJson TextDocumentContentChangeEvent :=
⟨fun j =>
  (do
    range ← j.getObjValAs? Range "range";
    text ← j.getObjValAs? String "text";
    pure (TextDocumentContentChangeEvent.rangeChange range text)) <|>
  (do
    text ← j.getObjValAs? String "text";
    pure (TextDocumentContentChangeEvent.fullChange text))⟩

instance didChangeTextDocumentParamsHasFromJson : HasFromJson DidChangeTextDocumentParams :=
⟨fun j => do
  textDocument ← j.getObjValAs? VersionedTextDocumentIdentifier "textDocument";
  contentChanges ← j.getObjValAs? (Array TextDocumentContentChangeEvent) "contentChanges";
  pure ⟨textDocument, contentChanges⟩⟩

instance didCloseTextDocumentParamsHasFromJson : HasFromJson DidCloseTextDocumentParams :=
⟨fun j => do
  textDocument ← j.getObjValAs? TextDocumentIdentifier "textDocument";
  pure ⟨textDocument⟩⟩

end Lean.Lsp
