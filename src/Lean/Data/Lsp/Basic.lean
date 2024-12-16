/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
prelude
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
  deriving Inhabited, BEq, Ord, Hashable, ToJson, FromJson, Repr

instance : ToString Position := ⟨fun p =>
  "(" ++ toString p.line ++ ", " ++ toString p.character ++ ")"⟩

instance : LT Position := ltOfOrd
instance : LE Position := leOfOrd

structure Range where
  start : Position
  «end» : Position
  deriving Inhabited, BEq, Hashable, ToJson, FromJson, Ord, Repr

instance : LT Range := ltOfOrd
instance : LE Range := leOfOrd

/-- A `Location` is a `DocumentUri` and a `Range`. -/
structure Location where
  uri : DocumentUri
  range : Range
  deriving Inhabited, BEq, ToJson, FromJson, Ord

structure LocationLink where
  originSelectionRange? : Option Range
  targetUri : DocumentUri
  targetRange : Range
  targetSelectionRange : Range
  deriving ToJson, FromJson

-- NOTE: Diagnostic defined in Diagnostics.lean

/-- Represents a reference to a client editor command.

NOTE: No specific commands are specified by LSP, hence
possible commands need to be announced as capabilities.

[reference](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#command)
-/
structure Command where
  /-- Title of the command, like `save`. -/
  title : String
  /-- The identifier of the actual command handler. -/
  command : String
  /-- Arguments that the command handler should be invoked with. -/
  arguments? : Option (Array Json) := none
  deriving ToJson, FromJson

/-- A snippet is a string that gets inserted into a document,
and can afterwards be edited by the user in a structured way.

Snippets contain instructions that
specify how this structured editing should proceed.
They are expressed in a domain-specific language
based on one from TextMate,
including the following constructs:
- Designated positions for subsequent user input,
  called "tab stops" after their most frequently-used keybinding.
  They are denoted with `$1`, `$2`, and so forth.
  `$0` denotes where the cursor should be positioned after all edits are completed,
  defaulting to the end of the string.
  Snippet tab stops are unrelated to tab stops used for indentation.
- Tab stops with default values, called _placeholders_, written `${1:default}`.
  The default may itself contain a tab stop or a further placeholder
  and multiple options to select from may be provided
  by surrounding them with `|`s and separating them with `,`,
  as in `${1|if $2 then $3 else $4,if let $2 := $3 then $4 else $5|}`.
- One of a set of predefined variables that are replaced with their values.
  This includes the current line number (`$TM_LINE_NUMBER`)
  or the text that was selected when the snippet was invoked (`$TM_SELECTED_TEXT`).
- Formatting instructions to modify variables using regular expressions
  or a set of predefined filters.

The full syntax and semantics of snippets,
including the available variables and the rules for escaping control characters,
are described in the [LSP specification](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#snippet_syntax). -/
structure SnippetString where
  value : String
  deriving ToJson, FromJson

/-- A textual edit applicable to a text document.

[reference](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textEdit) -/
structure TextEdit where
  /--  The range of the text document to be manipulated.
    To insert text into a document create a range where `start = end`. -/
  range : Range
  /-- The string to be inserted. For delete operations use an empty string. -/
  newText : String
  /-- If this field is present and the editor supports it,
  `newText` is ignored
  and an interactive snippet edit is performed instead.

  The use of snippets in `TextEdit`s
  is a Lean-specific extension to the LSP standard,
  so `newText` should still be set to a correct value
  as fallback in case the editor does not support this feature.
  Even editors that support snippets may not always use them;
  for instance, if the file is not already open,
  VS Code will perform a normal text edit in the background instead. -/
  /- NOTE: Similar functionality may be added to LSP in the future:
  see [issue #592](https://github.com/microsoft/language-server-protocol/issues/592).
  If such an addition occurs, this field should be deprecated. -/
  leanExtSnippet? : Option SnippetString := none
  /-- Identifier for annotated edit.

    `WorkspaceEdit` has a `changeAnnotations` field that maps these identifiers to a `ChangeAnnotation`.
    By annotating an edit you can add a description of what the edit will do and also control whether the
    user is presented with a prompt before applying the edit.
    [reference](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textEdit).
  -/
  annotationId? : Option String := none
  deriving ToJson, FromJson

/-- An array of `TextEdit`s to be performed in sequence. -/
def TextEditBatch := Array TextEdit

instance : FromJson TextEditBatch :=
  ⟨@fromJson? (Array TextEdit) _⟩

instance : ToJson TextEditBatch :=
  ⟨@toJson (Array TextEdit) _⟩

instance : EmptyCollection TextEditBatch := ⟨#[]⟩

instance : Append TextEditBatch :=
  inferInstanceAs (Append (Array _))

instance : Coe TextEdit TextEditBatch where
  coe te := #[te]

structure TextDocumentIdentifier where
  uri : DocumentUri
  deriving ToJson, FromJson

structure VersionedTextDocumentIdentifier where
  uri : DocumentUri
  version? : Option Nat := none
  deriving ToJson, FromJson

/-- A batch of `TextEdit`s to perform on a versioned text document.

[reference](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocumentEdit) -/
structure TextDocumentEdit where
  textDocument : VersionedTextDocumentIdentifier
  edits : TextEditBatch
  deriving ToJson, FromJson

/-- Additional information that describes document changes.

[reference](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textEdit) -/
structure ChangeAnnotation where
  /-- A human-readable string describing the actual change.
  The string is rendered prominent in the user interface. -/
  label             : String
  /-- A flag which indicates that user confirmation is needed before applying the change. -/
  needsConfirmation : Bool := false
  /-- A human-readable string which is rendered less prominent in the user interface. -/
  description?      : Option String := none
  deriving ToJson, FromJson

/-- Options for `CreateFile` and `RenameFile`. -/
structure CreateFile.Options where
  overwrite      : Bool := false
  ignoreIfExists : Bool := false
  deriving ToJson, FromJson

/-- Options for `DeleteFile`. -/
structure DeleteFile.Options where
  recursive : Bool := false
  ignoreIfNotExists := false
  deriving ToJson, FromJson

structure CreateFile where
  uri           : DocumentUri
  options?      : Option CreateFile.Options := none
  annotationId? : Option String := none
  deriving ToJson, FromJson

structure RenameFile where
  oldUri        : DocumentUri
  newUri        : DocumentUri
  options?      : Option CreateFile.Options := none
  annotationId? : Option String := none
  deriving ToJson, FromJson

structure DeleteFile where
  uri           : DocumentUri
  options?      : Option DeleteFile.Options := none
  annotationId? : Option String := none
  deriving ToJson, FromJson

/-- A change to a file resource.

[reference](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#resourceChanges) -/
inductive DocumentChange where
  | create : CreateFile       → DocumentChange
  | rename : RenameFile       → DocumentChange
  | delete : DeleteFile       → DocumentChange
  | edit   : TextDocumentEdit → DocumentChange

instance : ToJson DocumentChange := ⟨fun
  | .create x => Json.setObjVal! (toJson x) "kind" "create"
  | .rename x => Json.setObjVal! (toJson x) "kind" "rename"
  | .delete x => Json.setObjVal! (toJson x) "kind" "delete"
  | .edit   x => toJson x
⟩

instance : FromJson DocumentChange where
  fromJson? j := (do
    let kind ← j.getObjVal? "kind"
    match kind with
      | "create" => return DocumentChange.create <|← fromJson? j
      | "rename" => return DocumentChange.rename <|← fromJson? j
      | "delete" => return DocumentChange.delete <|← fromJson? j
      | kind => throw s!"Unrecognized kind: {kind}")
    <|> (DocumentChange.edit <$> fromJson? j)

/-- A workspace edit represents changes to many resources managed in the workspace.

[reference](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#workspaceEdit) -/
structure WorkspaceEdit where
  /-- Changes to existing resources. -/
  changes? : Option (RBMap DocumentUri TextEditBatch compare) := none
  /-- Depending on the client capability
    `workspace.workspaceEdit.resourceOperations` document changes are either
    an array of `TextDocumentEdit`s to express changes to n different text
    documents where each text document edit addresses a specific version of
    a text document. Or it can contain above `TextDocumentEdit`s mixed with
    create, rename and delete file / folder operations.

    Whether a client supports versioned document edits is expressed via
    `workspace.workspaceEdit.documentChanges` client capability.

    If a client neither supports `documentChanges` nor
    `workspace.workspaceEdit.resourceOperations` then only plain `TextEdit`s
    using the `changes` property are supported. -/
  documentChanges? : Option (Array DocumentChange) := none
  /-- A map of change annotations that can be referenced in
      `AnnotatedTextEdit`s or create, rename and delete file / folder
      operations.

      Whether clients honor this property depends on the client capability
      `workspace.changeAnnotationSupport`. -/
  changeAnnotations? : Option (RBMap String ChangeAnnotation compare) := none
  deriving ToJson, FromJson

namespace WorkspaceEdit

instance : EmptyCollection WorkspaceEdit := ⟨{}⟩

instance : Append WorkspaceEdit where
  append x y := {
    changes?           :=
      match x.changes?, y.changes? with
      | v, none | none, v => v
      | some x, some y => x.mergeBy (fun _ v₁ v₂ => v₁ ++ v₂) y
    documentChanges?   :=
      match x.documentChanges?, y.documentChanges? with
      | v, none | none, v => v
      | some x, some y => x ++ y
    changeAnnotations? :=
      match x.changeAnnotations?, y.changeAnnotations? with
      | v, none | none, v => v
      | some x, some y => x.mergeBy (fun _ _v₁ v₂ => v₂) y
  }

def ofTextDocumentEdit (e : TextDocumentEdit) : WorkspaceEdit :=
  { documentChanges? := #[DocumentChange.edit e]}

def ofTextEdit (doc : VersionedTextDocumentIdentifier) (te : TextEdit) : WorkspaceEdit :=
  ofTextDocumentEdit { textDocument := doc, edits := #[te]}

end WorkspaceEdit

/-- The `workspace/applyEdit` request is sent from the server to the client to modify resource on the client side.

[reference](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#applyWorkspaceEditParams) -/
structure ApplyWorkspaceEditParams where
  /-- An optional label of the workspace edit. This label is
  presented in the user interface for example on an undo
  stack to undo the workspace edit. -/
  label? : Option String := none
  /-- The edits to apply. -/
  edit : WorkspaceEdit
  deriving ToJson, FromJson

/-- An item to transfer a text document from the client to the server.

[reference](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocumentItem)
-/
structure TextDocumentItem where
  /-- The text document's URI. -/
  uri : DocumentUri
  /-- The text document's language identifier. -/
  languageId : String
  /-- The version number of this document (it will increase after each change, including undo/redo). -/
  version : Nat
  /-- The content of the opened text document. -/
  text : String
  deriving ToJson, FromJson

structure TextDocumentPositionParams where
  textDocument : TextDocumentIdentifier
  position : Position
  deriving ToJson, FromJson

instance : ToString TextDocumentPositionParams where
  toString p := s!"{p.textDocument.uri}:{p.position.line}:{p.position.character}"

structure DocumentFilter where
  language? : Option String := none
  scheme?   : Option String := none
  pattern?  : Option String := none
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
  deriving DecidableEq, Hashable

instance : FromJson MarkupKind := ⟨fun
  | str "plaintext" => Except.ok MarkupKind.plaintext
  | str "markdown"  => Except.ok MarkupKind.markdown
  | _               => throw "unknown MarkupKind"⟩

instance : ToJson MarkupKind := ⟨fun
  | MarkupKind.plaintext => str "plaintext"
  | MarkupKind.markdown  => str "markdown"⟩

structure MarkupContent where
  kind  : MarkupKind
  value : String
  deriving ToJson, FromJson, DecidableEq, Hashable

/-- Reference to the progress of some in-flight piece of work.

[reference](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#progress)
-/
abbrev ProgressToken := String -- do we need integers?

/-- Params for JSON-RPC method `$/progress` request.

[reference](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#progress) -/
structure ProgressParams (α : Type) where
  token : ProgressToken
  value : α
  deriving ToJson

structure WorkDoneProgressReport where
  kind := "report"
  /-- More detailed associated progress message. -/
  message? : Option String := none
  /-- Controls if a cancel button should show to allow the user to cancel the operation. -/
  cancellable := false
  /-- Optional progress percentage to display (value 100 is considered 100%).
      If not provided infinite progress is assumed. -/
  percentage? : Option Nat := none
  deriving ToJson

/-- Notification to signal the start of progress reporting. -/
structure WorkDoneProgressBegin extends WorkDoneProgressReport where
  kind := "begin"
  title : String
  deriving ToJson

/-- Signals the end of progress reporting. -/
structure WorkDoneProgressEnd where
  kind := "end"
  message? : Option String := none
  deriving ToJson

structure WorkDoneProgressParams where
  workDoneToken? : Option ProgressToken := none
  deriving ToJson, FromJson

structure PartialResultParams where
  partialResultToken? : Option ProgressToken := none
  deriving ToJson, FromJson

/-- [reference](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#workDoneProgressOptions) -/
structure WorkDoneProgressOptions where
  workDoneProgress := false
  deriving ToJson, FromJson

end Lsp
end Lean
