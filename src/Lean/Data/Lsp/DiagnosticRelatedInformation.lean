/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki, Willem Vanhulle
-/
module

prelude
public import Lean.Data.Lsp.Basic

public section

/-! LSP diagnostic related information.

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
