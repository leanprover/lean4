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

inductive DiagnosticSeverity where
  | error | warning | information | hint
  deriving Inhabited, BEq

instance : FromJson DiagnosticSeverity := ⟨fun j =>
  match j.getNat? with
  | Except.ok 1 => DiagnosticSeverity.error
  | Except.ok 2 => DiagnosticSeverity.warning
  | Except.ok 3 => DiagnosticSeverity.information
  | Except.ok 4 => DiagnosticSeverity.hint
  | _           => throw s!"unknown DiagnosticSeverity '{j}'"⟩

instance : ToJson DiagnosticSeverity := ⟨fun
  | DiagnosticSeverity.error       => 1
  | DiagnosticSeverity.warning     => 2
  | DiagnosticSeverity.information => 3
  | DiagnosticSeverity.hint        => 4⟩

inductive DiagnosticCode where
  | int (i : Int)
  | string (s : String)
  deriving Inhabited, BEq

instance : FromJson DiagnosticCode := ⟨fun
  | num (i : Int) => DiagnosticCode.int i
  | str s         => DiagnosticCode.string s
  | j             => throw s!"expected string or integer diagnostic code, got '{j}'"⟩

instance : ToJson DiagnosticCode := ⟨fun
  | DiagnosticCode.int i    => i
  | DiagnosticCode.string s => s⟩

inductive DiagnosticTag where
  | unnecessary
  | deprecated
  deriving Inhabited, BEq

instance : FromJson DiagnosticTag := ⟨fun j =>
  match j.getNat? with
  | Except.ok 1 => DiagnosticTag.unnecessary
  | Except.ok 2 => DiagnosticTag.deprecated
  | _      => throw "unknown DiagnosticTag"⟩

instance : ToJson DiagnosticTag := ⟨fun
  | DiagnosticTag.unnecessary => (1 : Nat)
  | DiagnosticTag.deprecated  => (2 : Nat)⟩

structure DiagnosticRelatedInformation where
  location : Location
  message : String
  deriving Inhabited, BEq, ToJson, FromJson

structure DiagnosticWith (α : Type) where
  range : Range
  /-- Extension: preserve semantic range of errors when truncating them for display purposes. -/
  fullRange : Range := range
  severity? : Option DiagnosticSeverity := none
  code? : Option DiagnosticCode := none
  source? : Option String := none
  /-- Parametrised by the type of message data. LSP diagnostics use `String`,
  whereas in Lean's interactive diagnostics we use the type of widget-enriched text.
  See `Lean.Widget.InteractiveDiagnostic`. -/
  message : α
  tags? : Option (Array DiagnosticTag) := none
  relatedInformation? : Option (Array DiagnosticRelatedInformation) := none
  deriving Inhabited, BEq, ToJson, FromJson

abbrev Diagnostic := DiagnosticWith String

structure PublishDiagnosticsParams where
  uri : DocumentUri
  version? : Option Int := none
  diagnostics: Array Diagnostic
  deriving Inhabited, BEq, ToJson, FromJson

end Lsp
end Lean
