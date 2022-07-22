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

inductive TextDocumentSyncKind where
  | none
  | full
  | incremental

instance : FromJson TextDocumentSyncKind := ⟨fun j =>
  match j.getNat? with
  | Except.ok 0 => return TextDocumentSyncKind.none
  | Except.ok 1 => return TextDocumentSyncKind.full
  | Except.ok 2 => return TextDocumentSyncKind.incremental
  | _      => throw "unknown TextDocumentSyncKind"⟩

instance : ToJson TextDocumentSyncKind := ⟨fun
  | TextDocumentSyncKind.none        => 0
  | TextDocumentSyncKind.full        => 1
  | TextDocumentSyncKind.incremental => 2⟩

structure DidOpenTextDocumentParams where
  textDocument : TextDocumentItem
  deriving ToJson, FromJson

structure TextDocumentChangeRegistrationOptions where
  documentSelector? : Option DocumentSelector := none
  syncKind : TextDocumentSyncKind
  deriving FromJson

inductive TextDocumentContentChangeEvent where
  -- omitted: deprecated rangeLength
  | rangeChange (range : Range) (text : String)
  | fullChange (text : String)

instance : FromJson TextDocumentContentChangeEvent where
  fromJson? j :=
    (do
      let range ← j.getObjValAs? Range "range"
      let text ← j.getObjValAs? String "text"
      return TextDocumentContentChangeEvent.rangeChange range text)
    <|>
    (TextDocumentContentChangeEvent.fullChange <$> j.getObjValAs? String "text")

instance TextDocumentContentChangeEvent.hasToJson : ToJson TextDocumentContentChangeEvent :=
  ⟨fun o => mkObj $ match o with
    | TextDocumentContentChangeEvent.rangeChange range text => [⟨"range", toJson range⟩, ⟨"text", toJson text⟩]
    | TextDocumentContentChangeEvent.fullChange text => [⟨"text", toJson text⟩]⟩

structure DidChangeTextDocumentParams where
  textDocument : VersionedTextDocumentIdentifier
  contentChanges : Array TextDocumentContentChangeEvent
  deriving ToJson, FromJson

-- TODO: missing:
-- WillSaveTextDocumentParams, TextDocumentSaveReason,
-- TextDocumentSaveRegistrationOptions, DidSaveTextDocumentParams

structure SaveOptions where
  includeText : Bool
  deriving ToJson, FromJson

structure DidCloseTextDocumentParams where
  textDocument : TextDocumentIdentifier
  deriving ToJson, FromJson

-- TODO: TextDocumentSyncClientCapabilities

/-- NOTE: This is defined twice in the spec. The latter version has more fields. -/
structure TextDocumentSyncOptions where
  openClose : Bool
  change : TextDocumentSyncKind
  willSave : Bool
  willSaveWaitUntil : Bool
  save? : Option SaveOptions := none
  deriving ToJson, FromJson

end Lsp
end Lean
