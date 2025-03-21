/-
Copyright (c) 2020 Marc Huisinga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Marc Huisinga, Wojciech Nawrocki
-/
prelude
import Lean.Data.Json
import Lean.Data.Lsp.Basic
import Lean.Data.Lsp.Utf16

import Lean.Message

/-! Definitions and functionality for emitting diagnostic information
such as errors, warnings and #command outputs from the LSP server.

[LSP: Diagnostic](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#diagnostic);
[LSP: `textDocument/publishDiagnostics`](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_publishDiagnostics)
-/

namespace Lean
namespace Lsp

open Json

inductive DiagnosticSeverity where
  | error | warning | information | hint
  deriving Inhabited, BEq, Ord

instance : FromJson DiagnosticSeverity := ⟨fun j =>
  match j.getNat? with
  | Except.ok 1 => return DiagnosticSeverity.error
  | Except.ok 2 => return DiagnosticSeverity.warning
  | Except.ok 3 => return DiagnosticSeverity.information
  | Except.ok 4 => return DiagnosticSeverity.hint
  | _           => throw s!"unknown DiagnosticSeverity '{j}'"⟩

instance : ToJson DiagnosticSeverity := ⟨fun
  | DiagnosticSeverity.error       => 1
  | DiagnosticSeverity.warning     => 2
  | DiagnosticSeverity.information => 3
  | DiagnosticSeverity.hint        => 4⟩

/-- Some languages have specific codes for each error type. -/
inductive DiagnosticCode where
  | int (i : Int)
  | string (s : String)
  deriving Inhabited, BEq, Ord

instance : FromJson DiagnosticCode := ⟨fun
  | num (i : Int) => return DiagnosticCode.int i
  | str s         => return DiagnosticCode.string s
  | j             => throw s!"expected string or integer diagnostic code, got '{j}'"⟩

instance : ToJson DiagnosticCode := ⟨fun
  | DiagnosticCode.int i    => i
  | DiagnosticCode.string s => s⟩

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

/--
Custom diagnostic tags provided by the language server.
We use a separate diagnostic field for this to avoid confusing LSP clients with our custom tags.
-/
inductive LeanDiagnosticTag where
  /--
  Diagnostics representing an "unsolved goals" error.
  Corresponds to `MessageData.tagged `Tactic.unsolvedGoals ..`.
  -/
  | unsolvedGoals
  /--
  Diagnostics representing a "goals accomplished" silent message.
  Corresponds to `MessageData.tagged `goalsAccomplished ..`.
  -/
  | goalsAccomplished
  deriving Inhabited, BEq, Ord

instance : FromJson LeanDiagnosticTag where
  fromJson? j :=
    match j.getNat? with
    | .ok 1 => return LeanDiagnosticTag.unsolvedGoals
    | .ok 2 => return LeanDiagnosticTag.goalsAccomplished
    | _     => throw "unknown LeanDiagnosticTag"

instance : ToJson LeanDiagnosticTag where
  toJson
  | .unsolvedGoals => (1 : Nat)
  | .goalsAccomplished => (2 : Nat)

/-- Represents a related message and source code location for a diagnostic.
    This should be used to point to code locations that cause or are related to
    a diagnostics, e.g when duplicating a symbol in a scope. -/
structure DiagnosticRelatedInformation where
  location : Location
  message : String
  deriving Inhabited, BEq, ToJson, FromJson, Ord

/-- Represents a diagnostic, such as a compiler error or warning. Diagnostic objects are only valid in the scope of a resource.

LSP accepts a `Diagnostic := DiagnosticWith String`.
The infoview also accepts `InteractiveDiagnostic := DiagnosticWith (TaggedText MsgEmbed)`.

[reference](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#diagnostic) -/
structure DiagnosticWith (α : Type) where
  /-- The range at which the message applies. -/
  range : Range
  /-- Extension: preserve semantic range of errors when truncating them for display purposes. -/
  fullRange? : Option Range := some range
  severity? : Option DiagnosticSeverity := none
  /--
  Extension: whether this diagnostic should not be displayed as a regular diagnostic in the editor.
  In VS Code, this means that the diagnostic does not have a squiggly and is not displayed in
  the InfoView under 'All Messages', but it is still displayed under 'Messages'.
  Defaults to `false`.
  -/
  isSilent? : Option Bool := none
  /-- The diagnostic's code, which might appear in the user interface. -/
  code? : Option DiagnosticCode := none
  /-- A human-readable string describing the source of this diagnostic, e.g. 'typescript' or 'super lint'. -/
  source? : Option String := none
  /-- Parametrised by the type of message data. LSP diagnostics use `String`,
  whereas in Lean's interactive diagnostics we use the type of widget-enriched text.
  See `Lean.Widget.InteractiveDiagnostic`. -/
  message : α
  /-- Additional metadata about the diagnostic. -/
  tags? : Option (Array DiagnosticTag) := none
  /-- Additional Lean-specific metadata about the diagnostic. -/
  leanTags? : Option (Array LeanDiagnosticTag) := none
  /-- An array of related diagnostic information, e.g. when symbol-names within a scope collide all definitions can be marked via this property. -/
  relatedInformation? : Option (Array DiagnosticRelatedInformation) := none
  /-- A data entry field that is preserved between a `textDocument/publishDiagnostics` notification and `textDocument/codeAction` request. -/
  data?: Option Json := none
  deriving Inhabited, BEq, ToJson, FromJson

def DiagnosticWith.fullRange (d : DiagnosticWith α) : Range :=
  d.fullRange?.getD d.range

attribute [local instance] Ord.arrayOrd in
/-- Restriction of `DiagnosticWith` to properties that are displayed to users in the InfoView. -/
private structure DiagnosticWith.UserVisible (α : Type) where
  range               : Range
  fullRange?          : Option Range
  severity?           : Option DiagnosticSeverity
  code?               : Option DiagnosticCode
  source?             : Option String
  message             : α
  tags?               : Option (Array DiagnosticTag)
  relatedInformation? : Option (Array DiagnosticRelatedInformation)
  deriving Ord

/-- Extracts user-visible properties from the given `DiagnosticWith`. -/
private def DiagnosticWith.UserVisible.ofDiagnostic (d : DiagnosticWith α)
    : DiagnosticWith.UserVisible α :=
  { d with }

/-- Compares `DiagnosticWith` instances modulo non-user-facing properties. -/
def compareByUserVisible [Ord α] (a b : DiagnosticWith α) : Ordering :=
  compare (DiagnosticWith.UserVisible.ofDiagnostic a) (DiagnosticWith.UserVisible.ofDiagnostic b)

abbrev Diagnostic := DiagnosticWith String

/-- Parameters for the [`textDocument/publishDiagnostics` notification](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_publishDiagnostics). -/
structure PublishDiagnosticsParams where
  uri : DocumentUri
  version? : Option Int := none
  diagnostics : Array Diagnostic
  deriving Inhabited, BEq, ToJson, FromJson

end Lsp
end Lean
