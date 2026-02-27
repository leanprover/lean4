module

prelude
public import Lean.Data.Lsp.Basic

public section

/-!LSP diagnostic related information.

Factored into its own module so that `Lean.Message` can use `DiagnosticRelatedInformation`
on `BaseMessage` without importing the full LSP diagnostics infrastructure.

[LSP: DiagnosticRelatedInformation](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#diagnosticRelatedInformation)
-/

namespace Lean.Lsp

/-- Represents a related message and source code location for a diagnostic. -/
structure DiagnosticRelatedInformation where
  location : Location
  message : String
  deriving Inhabited, BEq, ToJson, FromJson, Ord

end Lean.Lsp
