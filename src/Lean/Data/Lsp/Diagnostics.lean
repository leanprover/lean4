import Lean.Data.Json
import Lean.Data.Lsp.Structure

namespace Lean.Lsp

open Lean
open Lean.Json

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



end Lean.Lsp
