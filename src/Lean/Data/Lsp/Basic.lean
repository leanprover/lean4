/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Lean.Data.Json

/-! Defines most of the 'Basic Structures' in the LSP specification
(https://microsoft.github.io/language-server-protocol/specifications/specification-current/),
as well as some utilities.

Since LSP is Json-based, Ints/Nats are represented by Floats on the wire. -/

namespace Lean
namespace Lsp

open Json

abbrev DocumentUri := String

/-- An array of the lines in a text document.
Elements mustn't contain newline characters. -/
def DocumentText := Array String

/-- Can represent both a UTF-16 position - this is what LSP clients send -
and a codepoint position - what we use internally.
`character` is accepted liberally: actual character := min(line length, character) -/
structure Position := (line : Nat) (character : Nat)

instance Position.hasFromJson : HasFromJson Position :=
⟨fun j => do
  line ← j.getObjValAs? Nat "line";
  character ← j.getObjValAs? Nat "character";
  pure ⟨line, character⟩⟩

instance Position.hasToJson : HasToJson Position :=
⟨fun o => mkObj $
  [ ⟨"line", o.line⟩
  , ⟨"character", o.character⟩
  ]⟩

instance Position.hasToString : HasToString Position :=
⟨fun p => "(" ++ toString p.line ++ ", " ++ toString p.character ++ ")"⟩

namespace DocumentText

/-- Computes a linear position in `("\n".intercalate text.toList)`
from an LSP-style 0-indexed (ln, col) position. -/
def lnColToLinearPos (text : DocumentText) (pos : Position) : String.Pos :=
text.foldrRange 0 pos.line (fun ln acc => acc + ln.length + 1) pos.character

/-- An imprecise inverse of lnColToLinearPos.
Should only be used for debugging. -/
def linearPosToLnCol (text : DocumentText) (pos : String.Pos) : Position :=
let ⟨_, outPos⟩ : String.Pos × Position :=
  text.foldl
    (fun ⟨chrsLeft, p⟩ ln =>
      if chrsLeft = 0 then ⟨0, p⟩
      else if ln.length > chrsLeft then (0, { p with character := chrsLeft })
      else (chrsLeft - ln.length - 1, { p with line := p.line + 1 }))
    (pos, ⟨0, 0⟩);
  outPos

end DocumentText

structure Range := (start : Position) («end» : Position)

instance Range.hasFromJson : HasFromJson Range :=
⟨fun j => do
  start ← j.getObjValAs? Position "start";
  «end» ← j.getObjValAs? Position "end";
  pure ⟨start, «end»⟩⟩

instance Range.hasToJson : HasToJson Range :=
⟨fun o => mkObj $
  [ ⟨"start", toJson o.start⟩
  , ⟨"end", toJson o.«end»⟩
  ]⟩

structure Location := (uri : DocumentUri) (range : Range)

instance Location.hasFromJson : HasFromJson Location :=
⟨fun j => do
  uri ← j.getObjValAs? DocumentUri "uri";
  range ← j.getObjValAs? Range "range";
  pure ⟨uri, range⟩⟩

instance Location.hasToJson : HasToJson Location :=
⟨fun o => mkObj $
  [ ⟨"uri", toJson o.uri⟩
  , ⟨"range", toJson o.range⟩
  ]⟩

structure LocationLink :=
(originSelectionRange? : Option Range)
(targetUri : DocumentUri)
(targetRange : Range)
(targetSelectionRange : Range)

instance LocationLink.hasFromJson : HasFromJson LocationLink :=
⟨fun j => do
  let originSelectionRange? := j.getObjValAs? Range "originSelectionRange";
  targetUri ← j.getObjValAs? DocumentUri "targetUri";
  targetRange ← j.getObjValAs? Range "targetRange";
  targetSelectionRange ← j.getObjValAs? Range "targetSelectionRange";
  pure ⟨originSelectionRange?, targetUri, targetRange, targetSelectionRange⟩⟩

instance LocationLink.hasToJson : HasToJson LocationLink :=
⟨fun o => mkObj $
  opt "originSelectionRange" o.originSelectionRange? ++
  [ ⟨"targetUri", toJson o.targetUri⟩
  , ⟨"targetRange", toJson o.targetRange⟩
  , ⟨"targetSelectionRange", toJson o.targetSelectionRange⟩
  ]⟩

-- NOTE: Diagnostic defined in Diagnostics.lean

/- NOTE: No specific commands are specified by LSP, hence
possible commands need to be announced as capabilities. -/
structure Command :=
(title : String)
(command : String)
(arguments? : Option (Array Json) := none)

instance Command.hasFromJson : HasFromJson Command :=
⟨fun j => do
  title ← j.getObjValAs? String "title";
  command ← j.getObjValAs? String "command";
  let arguments? := j.getObjValAs? (Array Json) "arguments";
  pure ⟨title, command, arguments?⟩⟩

instance Command.hasToJson : HasToJson Command :=
⟨fun o => mkObj $
  opt "arguments" o.arguments? ++
  [ ⟨"title", o.title⟩
  , ⟨"command", o.command⟩
  ]⟩

structure TextEdit :=
(range : Range)
(newText : String)

instance TextEdit.hasFromJson : HasFromJson TextEdit :=
⟨fun j => do
  range ← j.getObjValAs? Range "range";
  newText ← j.getObjValAs? String "newText";
  pure ⟨range, newText⟩⟩

instance TextEdit.hasToJson : HasToJson TextEdit :=
⟨fun o => mkObj $
  [ ⟨"range", toJson o.range⟩
  , ⟨"newText", o.newText⟩
  ]⟩

def TextEditBatch := Array TextEdit

instance TextEditBatch.hasFromJson : HasFromJson TextEditBatch :=
⟨@fromJson? (Array TextEdit) _⟩

instance TextEditBatch.hasToJson : HasToJson TextEditBatch :=
⟨@toJson (Array TextEdit) _⟩

structure TextDocumentIdentifier := (uri : DocumentUri)

instance TextDocumentIdentifier.hasFromJson : HasFromJson TextDocumentIdentifier :=
⟨fun j => TextDocumentIdentifier.mk <$> j.getObjValAs? DocumentUri "uri"⟩

instance TextDocumentIdentifier.hasToJson : HasToJson TextDocumentIdentifier :=
⟨fun o => mkObj [⟨"uri", o.uri⟩]⟩

structure VersionedTextDocumentIdentifier :=
(uri : DocumentUri)
(version? : Option Nat := none)

instance VersionedTextDocumentIdentifier.hasFromJson : HasFromJson VersionedTextDocumentIdentifier :=
⟨fun j => do
  uri ← j.getObjValAs? DocumentUri "uri";
  let version? := j.getObjValAs? Nat "version";
  pure ⟨uri, version?⟩⟩

instance VersionedTextDocumentIdentifier.hasToJson : HasToJson VersionedTextDocumentIdentifier :=
⟨fun o => mkObj $
  opt "version" o.version? ++
  [⟨"uri", o.uri⟩]⟩

structure TextDocumentEdit :=
(textDocument : VersionedTextDocumentIdentifier)
(edits : TextEditBatch)

instance TextDocumentEdit.hasFromJson : HasFromJson TextDocumentEdit :=
⟨fun j => do
  textDocument ← j.getObjValAs? VersionedTextDocumentIdentifier "textDocument";
  edits ← j.getObjValAs? TextEditBatch "edits";
  pure ⟨textDocument, edits⟩⟩

instance TextDocumentEdit.hasToJson : HasToJson TextDocumentEdit :=
⟨fun o => mkObj $
  [ ⟨"textDocument", toJson o.textDocument⟩
  , ⟨"edits", toJson o.edits⟩
  ]⟩

-- TODO(Marc): missing:
-- File Resource Changes, WorkspaceEdit
-- both of these are pretty global, we can look at their
-- uses when single file behaviour works.

structure TextDocumentItem :=
(uri : DocumentUri)
(languageId : String)
(version : Nat)
(text : String)

instance TextDocumentItem.hasFromJson : HasFromJson TextDocumentItem :=
⟨fun j => do
  uri ← j.getObjValAs? DocumentUri "uri";
  languageId ← j.getObjValAs? String "languageId";
  version ← j.getObjValAs? Nat "version";
  text ← j.getObjValAs? String "text";
  pure ⟨uri, languageId, version, text⟩⟩

instance TextDocumentItem.hasToJson : HasToJson TextDocumentItem :=
⟨fun o => mkObj $
  [ ⟨"uri", o.uri⟩
  , ⟨"languageId", o.languageId⟩
  , ⟨"version", o.version⟩
  , ⟨"text", o.text⟩
  ]⟩

structure TextDocumentPositionParams :=
(textDocument : TextDocumentIdentifier)
(position : Position)

instance TextDocumentPositionParams.hasFromJson : HasFromJson TextDocumentPositionParams :=
⟨fun j => do
  textDocument ← j.getObjValAs? TextDocumentIdentifier "textDocument";
  position ← j.getObjValAs? Position "position";
  pure ⟨textDocument, position⟩⟩

instance TextDocumentPositionParams.hasToJson : HasToJson TextDocumentPositionParams :=
⟨fun o => mkObj $
  [ ⟨"textDocument", toJson o.textDocument⟩
  , ⟨"position", toJson o.position⟩
  ]⟩

structure DocumentFilter :=
(language? : Option String := none)
(scheme? : Option String := none)
(pattern? : Option String := none)

instance DocumentFilter.hasFromJson : HasFromJson DocumentFilter :=
⟨fun j => do
  let language? := j.getObjValAs? String "language";
  let scheme? := j.getObjValAs? String "scheme";
  let pattern? := j.getObjValAs? String "pattern";
  pure ⟨language?, scheme?, pattern?⟩⟩

instance DocumentFilter.hasToJson : HasToJson DocumentFilter :=
⟨fun o => mkObj $
  opt "language" o.language? ++
  opt "scheme" o.scheme? ++
  opt "pattern" o.pattern?⟩

def DocumentSelector := Array DocumentFilter

instance DocumentSelector.hasFromJson : HasFromJson DocumentSelector :=
⟨@fromJson? (Array DocumentFilter) _⟩

instance DocumentSelector.hasToJson : HasToJson DocumentSelector :=
⟨@toJson (Array DocumentFilter) _⟩

structure StaticRegistrationOptions := (id? : Option String := none)

instance StaticRegistrationOptions.hasFromJson : HasFromJson StaticRegistrationOptions :=
⟨fun j => some ⟨j.getObjValAs? String "id"⟩⟩

instance StaticRegistrationOptions.hasToJson : HasToJson StaticRegistrationOptions :=
⟨fun o => mkObj $ opt "id" o.id?⟩

structure TextDocumentRegistrationOptions := (documentSelector? : Option DocumentSelector := none)

instance TextDocumentRegistrationOptions.hasFromJson : HasFromJson TextDocumentRegistrationOptions :=
⟨fun j => some ⟨j.getObjValAs? DocumentSelector "documentSelector"⟩⟩

instance TextDocumentRegistrationOptions.hasToJson : HasToJson TextDocumentRegistrationOptions :=
⟨fun o => mkObj $ opt "documentSelector" o.documentSelector?⟩

inductive MarkupKind | plaintext | markdown

instance MarkupKind.hasFromJson : HasFromJson MarkupKind :=
⟨fun j => match j with
  | str "plaintext" => some MarkupKind.plaintext
  | str "markdown"  => some MarkupKind.markdown
  | _               => none⟩

instance MarkupKind.hasToJson : HasToJson MarkupKind :=
⟨fun k => match k with
  | MarkupKind.plaintext => str "plaintext"
  | MarkupKind.markdown  => str "markdown"⟩

structure MarkupContent := (kind : MarkupKind) (value : String)

instance MarkupContent.hasFromJson : HasFromJson MarkupContent :=
⟨fun j => do
  kind ← j.getObjValAs? MarkupKind "kind";
  value ← j.getObjValAs? String "value";
  pure ⟨kind, value⟩⟩

instance MarkupContent.hasToJson : HasToJson MarkupContent :=
⟨fun o => mkObj $
  [ ⟨"kind", toJson o.kind⟩
  , ⟨"value", o.value⟩
  ]⟩

-- TODO(Marc): missing:
-- WorkDoneProgressBegin, WorkDoneProgressReport,
-- WorkDoneProgressEnd, WorkDoneProgressParams,
-- WorkDoneProgressOptions, PartialResultParams
-- Progress can be implemented
-- later when the basic functionality stands.

end Lsp
end Lean
