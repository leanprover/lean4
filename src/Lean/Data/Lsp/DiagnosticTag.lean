/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki, Willem Vanhulle
-/
module

prelude
public import Lean.Data.Json.FromToJson.Basic

public section

/-! LSP diagnostic tags.

Factored into its own module so that `Lean.Message` can use `DiagnosticTag`
on `BaseMessage` without importing the full LSP diagnostics infrastructure.

[LSP: DiagnosticTag](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#diagnosticTag)
-/

namespace Lean.Lsp

/-- Tags representing additional metadata about the diagnostic. -/
inductive DiagnosticTag where
  /-- Unused or unnecessary code. Rendered as faded out eg for unused variables. -/
  | unnecessary
  /-- Deprecated or obsolete code. Rendered with a strike-through. -/
  | deprecated
  deriving Inhabited, BEq, Ord

instance : FromJson DiagnosticTag := ⟨fun j =>
  match j.getNat? with
  | Except.ok 1  => return DiagnosticTag.unnecessary
  | Except.ok 2  => return DiagnosticTag.deprecated
  | _            => throw "unknown DiagnosticTag"⟩

instance : ToJson DiagnosticTag := ⟨fun
  | DiagnosticTag.unnecessary   => (1 : Nat)
  | DiagnosticTag.deprecated    => (2 : Nat)⟩

end Lean.Lsp
