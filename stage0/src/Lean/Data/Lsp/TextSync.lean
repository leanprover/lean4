/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Lean.Data.Json
import Lean.Data.Lsp.Basic

/-! Section "Text Document Synchronization" of the LSP spec. -/

namespace Lean
namespace Lsp

open Json

inductive TextDocumentSyncKind
  | none
  | full
  | incremental

instance : FromJson TextDocumentSyncKind := ⟨fun j =>
  match j.getNat? with
  | some 0 => TextDocumentSyncKind.none
  | some 1 => TextDocumentSyncKind.full
  | some 2 => TextDocumentSyncKind.incremental
  | _      => none⟩

instance : ToJson TextDocumentSyncKind := ⟨fun o =>
  match o with
  | TextDocumentSyncKind.none        => 0
  | TextDocumentSyncKind.full        => 1
  | TextDocumentSyncKind.incremental => 2⟩

structure DidOpenTextDocumentParams :=
  (textDocument : TextDocumentItem)

instance : FromJson DidOpenTextDocumentParams := ⟨fun j =>
  DidOpenTextDocumentParams.mk <$> j.getObjValAs? TextDocumentItem "textDocument"⟩

instance : ToJson DidOpenTextDocumentParams := ⟨fun o =>
  mkObj $ [⟨"textDocument", toJson o.textDocument⟩]⟩

structure TextDocumentChangeRegistrationOptions :=
  (documentSelector? : Option DocumentSelector := none)
  (syncKind : TextDocumentSyncKind)

instance : FromJson TextDocumentChangeRegistrationOptions := ⟨fun j => do
  let documentSelector? := j.getObjValAs? DocumentSelector "documentSelector";
  let syncKind ← j.getObjValAs? TextDocumentSyncKind "syncKind";
  pure ⟨documentSelector?, syncKind⟩⟩

inductive TextDocumentContentChangeEvent
  -- omitted: deprecated rangeLength
  | rangeChange (range : Range) (text : String)
  | fullChange (text : String)

instance : FromJson TextDocumentContentChangeEvent := ⟨fun j =>
  (do
    let range ← j.getObjValAs? Range "range"
    let text ← j.getObjValAs? String "text"
    pure $ TextDocumentContentChangeEvent.rangeChange range text) <|>
  (TextDocumentContentChangeEvent.fullChange <$> j.getObjValAs? String "text")⟩

structure DidChangeTextDocumentParams :=
  (textDocument : VersionedTextDocumentIdentifier)
  (contentChanges : Array TextDocumentContentChangeEvent)

instance : FromJson DidChangeTextDocumentParams := ⟨fun j => do
  let textDocument ← j.getObjValAs? VersionedTextDocumentIdentifier "textDocument"
  let contentChanges ← j.getObjValAs? (Array TextDocumentContentChangeEvent) "contentChanges"
  pure ⟨textDocument, contentChanges⟩⟩

-- TODO: missing:
-- WillSaveTextDocumentParams, TextDocumentSaveReason,
-- TextDocumentSaveRegistrationOptions, DidSaveTextDocumentParams

structure SaveOptions := (includeText : Bool)

instance : ToJson SaveOptions := ⟨fun o =>
  mkObj $ [⟨"includeText", o.includeText⟩]⟩

structure DidCloseTextDocumentParams := (textDocument : TextDocumentIdentifier)

instance : FromJson DidCloseTextDocumentParams := ⟨fun j =>
  DidCloseTextDocumentParams.mk <$> j.getObjValAs? TextDocumentIdentifier "textDocument"⟩

-- TODO: TextDocumentSyncClientCapabilities

/- NOTE: This is defined twice in the spec. The latter version has more fields. -/
structure TextDocumentSyncOptions :=
  (openClose : Bool)
  (change : TextDocumentSyncKind)
  (willSave : Bool)
  (willSaveWaitUntil : Bool)
  (save? : Option SaveOptions := none)

instance : ToJson TextDocumentSyncOptions := ⟨fun o =>
  mkObj $
    opt "save" o.save? ++ [
      ⟨"openClose", toJson o.openClose⟩,
      ⟨"change", toJson o.change⟩,
      ⟨"willSave", toJson o.willSave⟩,
      ⟨"willSaveWaitUntil", toJson o.willSaveWaitUntil⟩]⟩

end Lsp
end Lean
