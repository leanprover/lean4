import Lean.Data.Json

namespace Lean.Lsp

open Lean
open Lean.Json

-- all Ints/Nats in this file are Floats in LSP

-- as in http://tools.ietf.org/html/rfc3986
abbrev DocumentUri := String

-- LSP indexes text with rows and colums
abbrev DocumentText := Array String

-- character is accepted liberally: actual character := min(line length, character)
structure Position := (line : Nat) (character : Nat)

instance positionHasFromJson : HasFromJson Position :=
⟨fun j => do
  line ← j.getObjValAs? Nat "line";
  character ← j.getObjValAs? Nat "character";
  pure ⟨line, character⟩⟩

namespace Position

/-- Computes a linear position from an LSP-style 0-indexed (ln, col) position
and the text. -/
def lnColToLinearPos (pos : Position) (text : DocumentText) : String.Pos :=
text.foldrRange 0 pos.line (fun ln acc => acc + ln.length + 1) pos.character

end Position

-- [start, end)
structure Range := (start : Position) («end» : Position)

structure Location := (uri : DocumentUri) (range : Range)

structure LocationLink :=
-- span in origin that is highlighted (e.g. underlined).
-- default for none: word range at mouse position
(originSelectionRange? : Option Range)
(targetUri : DocumentUri)
-- span in target that is displayed
(targetRange : Range)
-- span in target that is highlighted and focused when link is followed.
-- must be a subrange of targetRange
(targetSelectionRange : Range)


structure Command :=
(title : String)
-- no specific commands are specified by LSP, hence
-- possible commands need to be announced as capabilities
(command : String)
(arguments? : Option (Array Json) := none)

structure TextEdit :=
-- text insertion: start = end
(range : Range)
-- text deletion: empty string
(newText : String)

-- no intermediate states:
-- - ranges may not overlap
-- - multiple inserts can have the same starting position
-- - the order of the array induces the insert order
-- - a single remove or replace edit after an insert
--   can also have the same starting position as the insert
def TextEditBatch := Array TextEdit

structure TextDocumentIdentifier := (uri : DocumentUri)

instance textDocumentIdentifierHasFromJson : HasFromJson TextDocumentIdentifier :=
⟨fun j => do
  uri ← j.getObjValAs? DocumentUri "uri";
  pure ⟨uri⟩⟩

structure VersionedTextDocumentIdentifier :=
(uri : DocumentUri)
-- increases after each change, undo and redo
-- none used when a document is not open and the
-- disk content is the master
(version? : Option Nat := none)

structure TextDocumentEdit :=
(textDocument : VersionedTextDocumentIdentifier)
(edits : TextEditBatch)

-- TODO(Marc): missing:
-- File Resource Changes, WorkspaceEdit
-- both of these are pretty global, we can look at their
-- uses when single file behaviour works.

structure TextDocumentItem :=
(uri : DocumentUri)
-- used to identify documents on the server side
-- when handling more than language
(languageId : String)
-- increases after each change, undo and redo
(version : Nat)
(text : String)

-- parameter literal for requests
structure TextDocumentPositionParams :=
(textDocument : TextDocumentIdentifier)
(position : Position)

instance textDocumentPositionParamsHasFromJson : HasFromJson TextDocumentPositionParams :=
⟨fun j => do
  textDocument ← j.getObjValAs? TextDocumentIdentifier "textDocument";
  position ← j.getObjValAs? Position "position";
  pure ⟨textDocument, position⟩⟩

structure DocumentFilter :=
(language? : Option String := none) -- language id
-- uri scheme like 'file' or 'untitled'
(scheme? : Option String := none)
-- glob pattern, like *.{ts,js}
-- syntax:
-- - * for one or more chars
-- - ? for one char in path segment
-- - ** for zero or more chars
-- - {} for group conditions
-- - [] for range of character
-- - [!...] to negate range of characters
(pattern? : Option String := none)

def DocumentSelector := Array DocumentFilter

structure TextDocumentRegistrationOptions := (documentSelector? : Option DocumentSelector := none)

-- TODO(Marc): missing:
-- StaticRegistrationOptions,
-- MarkupContent, WorkDoneProgressBegin, WorkDoneProgressReport,
-- WorkDoneProgressEnd, WorkDoneProgressParams,
-- WorkDoneProgressOptions, PartialResultParams
-- Markup and Progress can be implemented
-- later when the basic functionality stands.

instance documentUriHasFromJson : HasFromJson DocumentUri :=
⟨fun j => j.getStr?⟩

instance rangeHasFromJson : HasFromJson Range :=
⟨fun j => do
  start ← j.getObjValAs? Position "start";
  «end» ← j.getObjValAs? Position "end";
  pure ⟨start, «end»⟩⟩

instance locationHasFromJson : HasFromJson Location :=
⟨fun j => do
  uri ← j.getObjValAs? DocumentUri "uri";
  range ← j.getObjValAs? Range "range";
  pure ⟨uri, range⟩⟩

instance versionedTextDocumentIdentifierHasFromJson : HasFromJson VersionedTextDocumentIdentifier :=
⟨fun j => do
  uri ← j.getObjValAs? DocumentUri "uri";
  let version? := j.getObjValAs? Nat "version";
  pure ⟨uri, version?⟩⟩

instance textDocumentItemHasFromJson : HasFromJson TextDocumentItem :=
⟨fun j => do
  uri ← j.getObjValAs? DocumentUri "uri";
  languageId ← j.getObjValAs? String "languageId";
  version ← j.getObjValAs? Nat "version";
  text ← j.getObjValAs? String "text";
  pure ⟨uri, languageId, version, text⟩⟩

instance documentFilterHasFromJson : HasFromJson DocumentFilter :=
⟨fun j => do
  let language? := j.getObjValAs? String "language";
  let scheme? := j.getObjValAs? String "scheme";
  let pattern? := j.getObjValAs? String "pattern";
  pure ⟨language?, scheme?, pattern?⟩⟩

instance documentSelectorHasFromJson : HasFromJson DocumentSelector :=
⟨@fromJson? (Array DocumentFilter) _⟩

instance textDocumentRegistrationOptionsHasFromJson : HasFromJson TextDocumentRegistrationOptions :=
⟨fun j => some ⟨j.getObjValAs? DocumentSelector "documentSelector"⟩⟩

instance documentUriHasToJson : HasToJson DocumentUri :=
⟨fun (o : String) => o⟩

instance positionHasToJson : HasToJson Position :=
⟨fun o => mkObj $
  ⟨"line", o.line⟩ :: ⟨"character", o.character⟩ :: []⟩

instance rangeHasToJson : HasToJson Range :=
⟨fun o => mkObj $
  ⟨"start", toJson o.start⟩ :: ⟨"end", toJson o.«end»⟩ :: []⟩

instance locationHasToJson : HasToJson Location :=
⟨fun o => mkObj $
  ⟨"uri", toJson o.uri⟩ :: ⟨"range", toJson o.range⟩ :: []⟩

end Lean.Lsp
