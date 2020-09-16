/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
import Lean.Data.Json
import Lean.Data.Lsp.Basic
import Lean.Data.Lsp.Utf16

import Lean.Message

/-! Definitions and functionality for emitting diagnostic information
such as errors, warnings and #command outputs from the LSP server. -/

namespace Lean
namespace Lsp

open Json

inductive DiagnosticSeverity
| error | warning | information | hint

instance DiagnosticSeverity.hasFromJson : HasFromJson DiagnosticSeverity :=
⟨fun j => match j.getNat? with
  | some 1 => DiagnosticSeverity.error
  | some 2 => DiagnosticSeverity.warning
  | some 3 => DiagnosticSeverity.information
  | some 4 => DiagnosticSeverity.hint
  | _      => none⟩

instance DiagnosticSeverity.hasToJson : HasToJson DiagnosticSeverity :=
⟨fun o => match o with
  | DiagnosticSeverity.error       => (1 : Nat)
  | DiagnosticSeverity.warning     => (2 : Nat)
  | DiagnosticSeverity.information => (3 : Nat)
  | DiagnosticSeverity.hint        => (4 : Nat)⟩

inductive DiagnosticCode
| int (i : Int)
| string (s : String)

instance DiagnosticCode.hasFromJson : HasFromJson DiagnosticCode :=
⟨fun j => match j with
  | num (i : Int) => DiagnosticCode.int i
  | str s         => DiagnosticCode.string s
  | _             => none⟩

instance DiagnosticCode.hasToJson : HasToJson DiagnosticCode :=
⟨fun o => match o with
  | DiagnosticCode.int i    => i
  | DiagnosticCode.string s => s⟩

inductive DiagnosticTag
| unnecessary
| deprecated

instance DiagnosticTag.hasFromJson : HasFromJson DiagnosticTag :=
⟨fun j => match j.getNat? with
  | some 1 => DiagnosticTag.unnecessary
  | some 2 => DiagnosticTag.deprecated
  | _      => none⟩

instance DiagnosticTag.hasToJson : HasToJson DiagnosticTag :=
⟨fun o => match o with
  | DiagnosticTag.unnecessary => (1 : Nat)
  | DiagnosticTag.deprecated  => (2 : Nat)⟩

structure DiagnosticRelatedInformation :=
(location : Location)
(message : String)

instance DiagnosticRelatedInformation.hasFromJson : HasFromJson DiagnosticRelatedInformation :=
⟨fun j => do
  location ← j.getObjValAs? Location "location";
  message ← j.getObjValAs? String "message";
  pure ⟨location, message⟩⟩

instance DiagnosticRelatedInformation.hasToJson : HasToJson DiagnosticRelatedInformation :=
⟨fun o => mkObj [
  ⟨"location", toJson o.location⟩,
  ⟨"message", o.message⟩]⟩

structure Diagnostic :=
(range : Range)
(severity? : Option DiagnosticSeverity := none)
(code? : Option DiagnosticCode := none)
(source? : Option String := none)
(message : String)
(tags? : Option (Array DiagnosticTag) := none)
(relatedInformation? : Option (Array DiagnosticRelatedInformation) := none)

instance Diagnostic.hasFromJson : HasFromJson Diagnostic :=
⟨fun j => do
  range ← j.getObjValAs? Range "range";
  let severity? := j.getObjValAs? DiagnosticSeverity "severity";
  let code? := j.getObjValAs? DiagnosticCode "code";
  let source? := j.getObjValAs? String "source";
  message ← j.getObjValAs? String "message";
  let tags? := j.getObjValAs? (Array DiagnosticTag) "tags";
  let relatedInformation? := j.getObjValAs? (Array DiagnosticRelatedInformation) "relatedInformation";
  pure ⟨range, severity?, code?, source?, message, tags?, relatedInformation?⟩⟩

instance Diagnostic.hasToJson : HasToJson Diagnostic :=
⟨fun o => mkObj $
  opt "severity" o.severity? ++
  opt "code" o.code? ++
  opt "source" o.source? ++
  opt "tags" o.tags? ++
  opt "relatedInformation" o.relatedInformation? ++ [
    ⟨"range", toJson o.range⟩,
    ⟨"message", o.message⟩]⟩

structure PublishDiagnosticsParams :=
(uri : DocumentUri)
(version? : Option Int := none)
(diagnostics: Array Diagnostic)

instance PublishDiagnosticsParams.hasFromJson : HasFromJson PublishDiagnosticsParams :=
⟨fun j => do
  uri ← j.getObjValAs? DocumentUri "uri";
  let version? := j.getObjValAs? Int "version";
  diagnostics ← j.getObjValAs? (Array Diagnostic) "diagnostics";
  pure ⟨uri, version?, diagnostics⟩⟩

instance PublishDiagnosticsParams.hasToJson : HasToJson PublishDiagnosticsParams :=
⟨fun o => mkObj $
  opt "version" o.version? ++ [
    ⟨"uri", toJson o.uri⟩,
    ⟨"diagnostics", toJson o.diagnostics⟩]⟩

/-- Transform a Lean Message concerning the given text into an LSP Diagnostic. -/
def msgToDiagnostic (text : FileMap) (m : Message) : IO Diagnostic := do
let low : Lsp.Position := text.leanPosToLspPos m.pos;
let high : Lsp.Position := match m.endPos with
| some endPos => text.leanPosToLspPos endPos
| none        => low;
let range : Range := ⟨low, high⟩;
let severity := match m.severity with
| MessageSeverity.information => DiagnosticSeverity.information
| MessageSeverity.warning     => DiagnosticSeverity.warning
| MessageSeverity.error       => DiagnosticSeverity.error;
let source := "Lean 4 server";
message ← m.data.toString;
pure { range := range,
  severity? := severity,
  source? := source,
  message := message,
}

end Lsp
end Lean
