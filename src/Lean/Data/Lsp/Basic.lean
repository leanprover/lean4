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

/-- Data that comes with a $/cancelRequest -/
structure CancelParams where
  /-- The request id to cancel. -/
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

/-- A textual edit applicable to a text document. -/
structure TextEdit where
  /- The range of the text document to be manipulated. To insert
	text into a document create a range where start === end. -/
  range : Range
  /-- The string to be inserted. For delete operations use an
	empty string. -/
  newText : String
  deriving ToJson, FromJson

def TextEditBatch := Array TextEdit

instance : FromJson TextEditBatch :=
  ⟨@fromJson? (Array TextEdit) _⟩

instance  : ToJson TextEditBatch :=
  ⟨@toJson (Array TextEdit) _⟩

/-- Text documents are identified using a URI -/
structure TextDocumentIdentifier where
  /-- The text document's URI.-/
  uri : DocumentUri
  deriving ToJson, FromJson

/-- An identifier to denote a specific version of a text document -/
structure VersionedTextDocumentIdentifier extends TextDocumentIdentifier where
  /-- The version number of this document. -/
  version? : Option Nat := none
  deriving ToJson, FromJson

/-- Describes textual changes on a single text document. -/
structure TextDocumentEdit where
  /-- The text document to change. -/
  textDocument : VersionedTextDocumentIdentifier
  /-- The edits to be applied.  Note that Lean server does not support AnnotatedTextEdit -/
  edits : TextEditBatch
  deriving ToJson, FromJson

-- TODO(Marc): missing:
-- File Resource Changes, WorkspaceEdit
-- both of these are pretty global, we can look at their
-- uses when single file behaviour works.

/-- An item to transfer a text document from the client to the server. -/
structure TextDocumentItem where
  /-- The text document's URI. -/
  uri : DocumentUri
  /-- The text document's language identifier. -/
  languageId : String
  /-- The version number of this document. -/
  version : Nat
  /-- The content of the opened text document. -/
  text : String
  deriving ToJson, FromJson

/-- A parameter literal used in requests to pass a text document and a position inside that document -/
structure TextDocumentPositionParams where
  /-- The text document. -/
  textDocument : TextDocumentIdentifier
  /-- The position inside the text document. -/
  position : Position
  deriving ToJson, FromJson

/-- A document filter denotes a document through properties like language, scheme or pattern. -/
structure DocumentFilter where
  /-- A language id, like `typescript`.-/
  language? : Option String := none
  /--  A Uri scheme, like `file` or `untitled`.-/
  scheme? : Option String := none
  /-- A glob pattern, like `*.{ts,js}`. -/
  pattern? : Option String := none
  deriving ToJson, FromJson

/-- A document selector is the combination of one or more document filters. -/
def DocumentSelector := Array DocumentFilter

instance : FromJson DocumentSelector :=
  ⟨@fromJson? (Array DocumentFilter) _⟩

instance : ToJson DocumentSelector :=
  ⟨@toJson (Array DocumentFilter) _⟩

/-- Static registration options can be used to register a feature in the initialize result with a given server control
  ID to be able to un-register the feature later on.-/
structure StaticRegistrationOptions where
  /-- The id used to register the request. The id can be used to deregister
	the request again. -/
  id? : Option String := none
  deriving ToJson, FromJson

/-- Options to dynamically register for requests for a set of text documents. -/
structure TextDocumentRegistrationOptions where
  documentSelector? : Option DocumentSelector := none
  deriving ToJson, FromJson

inductive MarkupKind where
  | plaintext | markdown

instance : FromJson MarkupKind := ⟨fun
  | str "plaintext" => Except.ok MarkupKind.plaintext
  | str "markdown"  => Except.ok MarkupKind.markdown
  | _               => throw "unknown MarkupKind"⟩

/-- Describes the content type that a client supports in various
result literals like `Hover`, `ParameterInfo` or `CompletionItem`.-/
instance : ToJson MarkupKind := ⟨fun
  | MarkupKind.plaintext => str "plaintext"
  | MarkupKind.markdown  => str "markdown"⟩

/-- A MarkupContent literal represents a string value which content can be represented in different formats. -/
structure MarkupContent where
  kind : MarkupKind
  value : String
  deriving ToJson, FromJson

/-- Data sent with a $/progress request -/
structure ProgressParams (α : Type) where
  /-- The progress token provided by the client or server.-/
  token : String  -- do we need `integer`?
  /-- The progress data. -/
  value : α
  deriving ToJson

/-- The payload for progress report -/
structure WorkDoneProgressReport where
  kind := "report"
  /--  Optional, more detailed associated progress message. Contains
	complementary information to the `title`. -/
  message? : Option String := none
  /-- Controls enablement state of a cancel button. This property is only valid
	if a cancel button got requested in the `WorkDoneProgressBegin` payload. -/
  cancellable := false
  /-- Optional progress percentage to display (value 100 is considered 100%).
	If not provided infinite progress is assumed and clients are allowed
	to ignore the `percentage` value in subsequent in report notifications. -/
  percentage? : Option Nat := none
  deriving ToJson

/-- The payload of a $/progress notification -/
structure WorkDoneProgressBegin extends WorkDoneProgressReport where
  kind := "begin"
  /--  Mandatory title of the progress operation. Used to briefly inform about
	the kind of operation being performed.-/
  title : String
  deriving ToJson

/-- Signaling the end of a progress reporting is done using the following payload -/
structure WorkDoneProgressEnd where
  kind := "end"
  /-- Optional, a final message indicating to for example indicate the outcome
	of the operation.-/
  message? : Option String := none
  deriving ToJson

structure WorkDoneProgressParams where
  /-- An optional token that a server can use to report work done progress.-/
  workDoneToken?: Option String := none
  deriving ToJson

/-- The server progress capability -/
structure WorkDoneProgressOptions where
  workDoneProgress?: Option Bool := false
  deriving ToJson


end Lsp
end Lean
