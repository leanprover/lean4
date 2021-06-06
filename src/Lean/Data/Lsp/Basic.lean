/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Lean.Data.Json
import Lean.Data.JsonRpc

/-! Defines most of the 'Basic Structures' in the LSP specification
(https://microsoft.github.io/language-server-protocol/specifications/specification-current/),
as well as some utilities.

Since LSP is Json-based, Ints/Nats are represented by Floats on the wire. -/

namespace Lean
namespace Lsp

open Json

structure CancelParams where
  id : JsonRpc.RequestID
  deriving Inhabited, BEq, ToJson, FromJson

abbrev DocumentUri := String

/-- We adopt the convention that zero-based UTF-16 positions as sent by LSP clients
are represented by `Lsp.Position` while internally we mostly use `String.Pos` UTF-8
offsets. For diagnostics, one-based `Lean.Position`s are used internally.
`character` is accepted liberally: actual character := min(line length, character) -/
structure Position where
  line : Nat
  character : Nat
  deriving Inhabited, BEq, ToJson, FromJson

instance : ToString Position := ⟨fun p =>
  "(" ++ toString p.line ++ ", " ++ toString p.character ++ ")"⟩

structure Range where
  start : Position
  «end» : Position
  deriving Inhabited, BEq, ToJson, FromJson

structure Location where
  uri : DocumentUri
  range : Range
  deriving Inhabited, BEq, ToJson, FromJson

structure LocationLink where
  originSelectionRange? : Option Range
  targetUri : DocumentUri
  targetRange : Range
  targetSelectionRange : Range
  deriving ToJson, FromJson

-- NOTE: Diagnostic defined in Diagnostics.lean

/- NOTE: No specific commands are specified by LSP, hence
possible commands need to be announced as capabilities. -/
structure Command where
  title : String
  command : String
  arguments? : Option (Array Json) := none
  deriving ToJson, FromJson

structure TextEdit where
  range : Range
  newText : String
  deriving ToJson, FromJson

def TextEditBatch := Array TextEdit

instance : FromJson TextEditBatch :=
  ⟨@fromJson? (Array TextEdit) _⟩

instance  : ToJson TextEditBatch :=
  ⟨@toJson (Array TextEdit) _⟩

structure TextDocumentIdentifier where
  uri : DocumentUri
  deriving ToJson, FromJson

structure VersionedTextDocumentIdentifier where
  uri : DocumentUri
  version? : Option Nat := none
  deriving ToJson, FromJson

structure TextDocumentEdit where
  textDocument : VersionedTextDocumentIdentifier
  edits : TextEditBatch
  deriving ToJson, FromJson

-- TODO(Marc): missing:
-- File Resource Changes, WorkspaceEdit
-- both of these are pretty global, we can look at their
-- uses when single file behaviour works.

structure TextDocumentItem where
  uri : DocumentUri
  languageId : String
  version : Nat
  text : String
  deriving ToJson, FromJson

structure TextDocumentPositionParams where
  textDocument : TextDocumentIdentifier
  position : Position
  deriving ToJson, FromJson

structure DocumentFilter where
  language? : Option String := none
  scheme? : Option String := none
  pattern? : Option String := none
  deriving ToJson, FromJson

def DocumentSelector := Array DocumentFilter

instance : FromJson DocumentSelector :=
  ⟨@fromJson? (Array DocumentFilter) _⟩

instance : ToJson DocumentSelector :=
  ⟨@toJson (Array DocumentFilter) _⟩

structure StaticRegistrationOptions where
  id? : Option String := none
  deriving ToJson, FromJson

structure TextDocumentRegistrationOptions where
  documentSelector? : Option DocumentSelector := none
  deriving ToJson, FromJson

inductive MarkupKind where
  | plaintext | markdown

instance : FromJson MarkupKind := ⟨fun
  | str "plaintext" => Except.ok MarkupKind.plaintext
  | str "markdown"  => Except.ok MarkupKind.markdown
  | _               => throw "unknown MarkupKind"⟩

instance : ToJson MarkupKind := ⟨fun
  | MarkupKind.plaintext => str "plaintext"
  | MarkupKind.markdown  => str "markdown"⟩

structure MarkupContent where
  kind : MarkupKind
  value : String
  deriving ToJson, FromJson

structure ProgressParams (α : Type) where
  token : String  -- do we need `integer`?
  value : α
  deriving ToJson

structure WorkDoneProgressReport where
  kind := "report"
  message? : Option String := none
  cancellable := false
  percentage? : Option Nat := none
  deriving ToJson

structure WorkDoneProgressBegin extends WorkDoneProgressReport where
  kind := "begin"
  title : String
  deriving ToJson

structure WorkDoneProgressEnd where
  kind := "end"
  message? : Option String := none
  deriving ToJson

-- TODO(Marc): missing:
-- WorkDoneProgressOptions, PartialResultParams

end Lsp
end Lean
