import Lean.Data.Json

namespace Lean.Lsp

open Lean
open Lean.Json

-- all Ints in this file are Floats in LSP

-- as in http://tools.ietf.org/html/rfc3986
abbrev DocumentUri := String

-- character is accepted liberally: actual character := min(line length, character)
structure Position := (line : Nat) (character : Nat)

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

inductive DiagnosticSeverity
| error | warning | information | hint

instance diagnosticSeverityHasFromJson : HasFromJson DiagnosticSeverity :=
⟨fun j => match j.getNat? with
  | some 1 => DiagnosticSeverity.error
  | some 2 => DiagnosticSeverity.warning
  | some 3 => DiagnosticSeverity.information
  | some 4 => DiagnosticSeverity.hint
  | _      => none⟩

instance diagnosticSeverityHasToJson : HasToJson DiagnosticSeverity :=
⟨fun o => match o with
  | DiagnosticSeverity.error       => (1 : Nat)
  | DiagnosticSeverity.warning     => (2 : Nat)
  | DiagnosticSeverity.information => (3 : Nat)
  | DiagnosticSeverity.hint        => (4 : Nat)⟩

inductive DiagnosticCode
| int (i : Int)
| string (s : String)

instance diagnosticCodeHasToJson : HasToJson DiagnosticCode :=
⟨fun o => match o with
  | DiagnosticCode.int i    => i
  | DiagnosticCode.string s => s⟩

inductive DiagnosticTag
/- Unused or unnecessary code.

Clients are allowed to render diagnostics with this tag faded out instead of having
an error squiggle. -/
| unnecessary
/- Deprecated or obsolete code.

Clients are allowed to rendered diagnostics with this tag strike through. -/
| deprecated

/- Represents a related message and source code location for a diagnostic. This should be
used to point to code locations that cause or are related to a diagnostics, e.g when duplicating
a symbol in a scope. -/
structure DiagnosticRelatedInformation :=
(location : Location)
(message : String)

structure Diagnostic :=
/- The range at which the message applies. -/
(range : Range)
/- The diagnostic's severity. Can be omitted. If omitted it is up to the
client to interpret diagnostics as error, warning, info or hint. -/
(severity? : Option DiagnosticSeverity := none)
/- The diagnostic's code, which might appear in the user interface. -/
(code? : Option DiagnosticCode := none)
/- A human-readable string describing the source of this
diagnostic, e.g. 'typescript' or 'super lint'. -/
(source? : Option String := none)
/- The diagnostic's message. -/
(message : String)
/- Additional metadata about the diagnostic.
@since 3.15.0 -/
(tags? : Option (Array DiagnosticTag) := none)
/- An array of related diagnostic information, e.g. when symbol-names within
a scope collide all definitions can be marked via this property. -/
(relatedInformation? : Option (Array DiagnosticRelatedInformation) := none)

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

structure VersionedTextDocumentIdentifier :=
(uri : DocumentUri)
-- increases after each change, undo and redo
-- none used when a document is not open and the
-- disk content is the master
(version? : Option Int := none)

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
(version : Int)
(text : String)

-- parameter literal for requests
structure TextDocumentPositionParams :=
(textDocument : TextDocumentIdentifier)
(position : Position)

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

instance positionHasFromJson : HasFromJson Position :=
⟨fun j => do
  line ← j.getObjValAs? Nat "line";
  character ← j.getObjValAs? Nat "character";
  pure ⟨line, character⟩⟩

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

instance diagnosticCodeHasFromJson : HasFromJson DiagnosticCode :=
⟨fun j => match j with
  | num (i : Int) => DiagnosticCode.int i
  | str s         => DiagnosticCode.string s
  | _             => none⟩

instance diagnosticTagFromJson : HasFromJson DiagnosticTag :=
⟨fun j => match j.getNat? with
  | some 1 => DiagnosticTag.unnecessary
  | some 2 => DiagnosticTag.deprecated
  | _      => none⟩

instance diagnosticRelatedInformationHasFromJson : HasFromJson DiagnosticRelatedInformation :=
⟨fun j => do
  location ← j.getObjValAs? Location "location";
  message ← j.getObjValAs? String "message";
  pure ⟨location, message⟩⟩

instance diagnosticHasFromJson : HasFromJson Diagnostic :=
⟨fun j => do
  range ← j.getObjValAs? Range "range";
  let severity? := j.getObjValAs? DiagnosticSeverity "severity";
  let code? := j.getObjValAs? DiagnosticCode "code";
  let source? := j.getObjValAs? String "source";
  message ← j.getObjValAs? String "message";
  let tags? := j.getObjValAs? (Array DiagnosticTag) "tags";
  let relatedInformation? := j.getObjValAs? (Array DiagnosticRelatedInformation) "relatedInformation";
  pure ⟨range, severity?, code?, source?, message, tags?, relatedInformation?⟩⟩

instance textDocumentIdentifierHasFromJson : HasFromJson TextDocumentIdentifier :=
⟨fun j => do
  uri ← j.getObjValAs? DocumentUri "uri";
  pure ⟨uri⟩⟩

instance versionedTextDocumentIdentifierHasFromJson : HasFromJson VersionedTextDocumentIdentifier :=
⟨fun j => do
  uri ← j.getObjValAs? DocumentUri "uri";
  let version? := j.getObjValAs? Int "version";
  pure ⟨uri, version?⟩⟩

instance textDocumentItemHasFromJson : HasFromJson TextDocumentItem :=
⟨fun j => do
  uri ← j.getObjValAs? DocumentUri "uri";
  languageId ← j.getObjValAs? String "languageId";
  version ← j.getObjValAs? Int "version";
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

instance diagnosticTagHasToJson : HasToJson DiagnosticTag :=
⟨fun o => match o with
  | DiagnosticTag.unnecessary => (1 : Nat)
  | DiagnosticTag.deprecated  => (2 : Nat)⟩

instance diagnosticRelatedInformationHasToJson : HasToJson DiagnosticRelatedInformation :=
⟨fun o => mkObj $
  ⟨"location", toJson o.location⟩ :: ⟨"message", o.message⟩ :: []⟩

instance diagnosticHasToJson : HasToJson Diagnostic :=
⟨fun o => mkObj $
  ⟨"range", toJson o.range⟩ :: opt "severity" o.severity? ++ opt "code" o.code? ++
    opt "source" o.source? ++ ⟨"message", o.message⟩ :: opt "tags" o.tags? ++ []⟩

end Lean.Lsp
