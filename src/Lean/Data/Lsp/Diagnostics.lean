import Lean.Message
import Lean.Data.Json
import Lean.Data.Lsp.Structure
import Lean.Data.Lsp.Utf16

namespace Lean
namespace Lsp

open Json

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

instance diagnosticCodeHasFromJson : HasFromJson DiagnosticCode :=
⟨fun j => match j with
  | num (i : Int) => DiagnosticCode.int i
  | str s         => DiagnosticCode.string s
  | _             => none⟩

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

instance diagnosticTagHasFromJson : HasFromJson DiagnosticTag :=
⟨fun j => match j.getNat? with
  | some 1 => DiagnosticTag.unnecessary
  | some 2 => DiagnosticTag.deprecated
  | _      => none⟩

instance diagnosticTagHasToJson : HasToJson DiagnosticTag :=
⟨fun o => match o with
  | DiagnosticTag.unnecessary => (1 : Nat)
  | DiagnosticTag.deprecated  => (2 : Nat)⟩

/- Represents a related message and source code location for a diagnostic. This should be
used to point to code locations that cause or are related to a diagnostics, e.g when duplicating
a symbol in a scope. -/
structure DiagnosticRelatedInformation :=
(location : Location)
(message : String)

instance diagnosticRelatedInformationHasFromJson : HasFromJson DiagnosticRelatedInformation :=
⟨fun j => do
  location ← j.getObjValAs? Location "location";
  message ← j.getObjValAs? String "message";
  pure ⟨location, message⟩⟩

instance diagnosticRelatedInformationHasToJson : HasToJson DiagnosticRelatedInformation :=
⟨fun o => mkObj $
  ⟨"location", toJson o.location⟩ :: ⟨"message", o.message⟩ :: []⟩

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

instance diagnosticHasToJson : HasToJson Diagnostic :=
⟨fun o => mkObj $
⟨"range", toJson o.range⟩ :: opt "severity" o.severity? ++ opt "code" o.code? ++
opt "source" o.source? ++ ⟨"message", o.message⟩ :: opt "tags" o.tags? ++ []⟩

structure PublishDiagnosticsParams :=
(uri : DocumentUri)
-- version number of document for which
-- diagnostics are published
(version? : Option Int := none)
(diagnostics: Array Diagnostic)

instance publishDiagnosticsParamsHasFromJson : HasFromJson PublishDiagnosticsParams :=
⟨fun j => do
  uri ← j.getObjValAs? DocumentUri "uri";
  let version? := j.getObjValAs? Int "version";
  diagnostics ← j.getObjValAs? (Array Diagnostic) "diagnostics";
  pure ⟨uri, version?, diagnostics⟩⟩

instance publishDiagnosticsParamsHasToJson : HasToJson PublishDiagnosticsParams :=
⟨fun o => mkObj $
  ⟨"uri", toJson o.uri⟩ :: opt "version" o.version? ++ ⟨"diagnostics", toJson o.diagnostics⟩ :: []⟩

/-- Transform a Lean Message into an LSP Diagnostic. -/
def msgToDiagnostic (text : DocumentText) (m : Message) : Diagnostic :=
-- Lean Message line numbers are 1-based while LSP Positions are 0-based.
let lowLn := m.pos.line - 1;
let low : Lsp.Position := ⟨lowLn, (text.get! lowLn).codepointPosToUtf16Pos m.pos.column⟩;
let high : Lsp.Position := match m.endPos with
| some endPos =>
let highLn := endPos.line - 1;
⟨highLn, (text.get! highLn).codepointPosToUtf16Pos endPos.column⟩
| none        => low;
let range : Range := ⟨low, high⟩;
let severity := match m.severity with
| MessageSeverity.information => DiagnosticSeverity.information
| MessageSeverity.warning     => DiagnosticSeverity.warning
| MessageSeverity.error       => DiagnosticSeverity.error;
let source := "Lean 4 server";
let message := toString (format m.data);
{ range := range
, severity? := severity
, source? := source
, message := message}

end Lsp
end Lean
