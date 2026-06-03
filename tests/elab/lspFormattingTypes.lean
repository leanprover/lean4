import Lean

/-!
Tests for the LSP `textDocument/formatting` protocol types in `Lean.Lsp`:
`FormattingOptions`, the `*FormattingParams` request types, the
`*FormattingOptions` server-capability types, and the formatting `*Provider?`
fields wired into `ServerCapabilities`.

These check both the exact wire shape against the LSP 3.17/3.18 specification and
that the derived `FromJson`/`ToJson` instances round-trip.
-/

open Lean Lsp

/-- `toJson` then `fromJson?` then `toJson` again yields the same `Json`. -/
private def roundTrips {α} [FromJson α] [ToJson α] (a : α) : Bool :=
  match (fromJson? (toJson a) : Except String α) with
  | .ok b => toJson a == toJson b
  | .error _ => false

/-! ## `FormattingOptions` -/

-- Minimal: the two required fields; optionals are omitted from the wire form.
#guard
  let o : FormattingOptions := { tabSize := 2, insertSpaces := true }
  toJson o == json% { "tabSize": 2, "insertSpaces": true }

-- Full: the optional `@since 3.15.0` fields are emitted when present.
#guard
  let o : FormattingOptions := {
    tabSize := 4, insertSpaces := false,
    trimTrailingWhitespace? := some true, insertFinalNewline? := some true,
    trimFinalNewlines? := some false }
  toJson o == json% { "tabSize": 4, "insertSpaces": false,
    "trimTrailingWhitespace": true, "insertFinalNewline": true,
    "trimFinalNewlines": false }

-- Parsing leaves absent optionals as `none`.
#guard
  match (fromJson? (json% { "tabSize": 2, "insertSpaces": true }) : Except String FormattingOptions) with
  | .ok o => o.tabSize == 2 && o.insertSpaces == true
      && o.trimTrailingWhitespace? == none && o.insertFinalNewline? == none
      && o.trimFinalNewlines? == none
  | .error _ => false

#guard roundTrips (α := FormattingOptions)
  { tabSize := 4, insertSpaces := false, trimTrailingWhitespace? := some true }

-- The spec's open `[key: string]` clause: server-specific keys are preserved
-- (not dropped) and kept out of the well-known fields.
#guard
  let j := json% { "tabSize": 2, "insertSpaces": true,
    "myServer.cleverness": 11, "myServer.style": "compact" }
  match (fromJson? j : Except String FormattingOptions) with
  | .ok o => o.tabSize == 2
      && o.additionalProperties == json% { "myServer.cleverness": 11, "myServer.style": "compact" }
  | .error _ => false

-- Extras are emitted alongside the well-known fields.
#guard
  let o : FormattingOptions := {
    tabSize := 2, insertSpaces := true
    additionalProperties := json% { "myServer.cleverness": 11 } }
  toJson o == json% { "tabSize": 2, "insertSpaces": true, "myServer.cleverness": 11 }

#guard roundTrips (α := FormattingOptions)
  { tabSize := 2, insertSpaces := true, additionalProperties := json% { "a": "b", "c": 3 } }

/-! ## Request params -/

#guard
  let p : DocumentFormattingParams := {
    textDocument := ⟨"file:///a.lean"⟩
    options := { tabSize := 2, insertSpaces := true } }
  toJson p == json% { "textDocument": { "uri": "file:///a.lean" },
    "options": { "tabSize": 2, "insertSpaces": true } }

#guard
  let p : DocumentRangeFormattingParams := {
    textDocument := ⟨"file:///a.lean"⟩
    range := ⟨⟨0, 0⟩, ⟨1, 0⟩⟩
    options := { tabSize := 2, insertSpaces := true } }
  toJson p == json% { "textDocument": { "uri": "file:///a.lean" },
    "range": { "start": { "line": 0, "character": 0 },
      "end": { "line": 1, "character": 0 } },
    "options": { "tabSize": 2, "insertSpaces": true } }

#guard
  let p : DocumentRangesFormattingParams := {
    textDocument := ⟨"file:///a.lean"⟩
    ranges := #[⟨⟨0, 0⟩, ⟨1, 0⟩⟩]
    options := { tabSize := 2, insertSpaces := true } }
  toJson p == json% { "textDocument": { "uri": "file:///a.lean" },
    "ranges": [ { "start": { "line": 0, "character": 0 },
      "end": { "line": 1, "character": 0 } } ],
    "options": { "tabSize": 2, "insertSpaces": true } }

-- `DocumentOnTypeFormattingParams` carries `position` and `ch`, and (unlike the
-- others) no `workDoneToken` mixin.
#guard
  let p : DocumentOnTypeFormattingParams := {
    textDocument := ⟨"file:///a.lean"⟩
    position := ⟨3, 5⟩
    ch := "}"
    options := { tabSize := 2, insertSpaces := true } }
  toJson p == json% { "textDocument": { "uri": "file:///a.lean" },
    "position": { "line": 3, "character": 5 },
    "ch": "}", "options": { "tabSize": 2, "insertSpaces": true } }

#guard roundTrips (α := DocumentFormattingParams)
  { textDocument := ⟨"file:///a.lean"⟩, options := { tabSize := 2, insertSpaces := true } }

/-! ## Server-capability options -/

#guard
  let o : DocumentOnTypeFormattingOptions :=
    { firstTriggerCharacter := "}", moreTriggerCharacter? := some #[";"] }
  toJson o == json% { "firstTriggerCharacter": "}", "moreTriggerCharacter": [ ";" ] }

#guard roundTrips (α := DocumentOnTypeFormattingOptions) { firstTriggerCharacter := "{" }
#guard roundTrips (α := DocumentRangeFormattingOptions) { rangesSupport? := some true }
#guard roundTrips (α := DocumentFormattingOptions) {}

/-! ## `ServerCapabilities` exposes the three formatting providers -/

#guard
  let caps : ServerCapabilities := {
    documentFormattingProvider? := some {}
    documentRangeFormattingProvider? := some {}
    documentOnTypeFormattingProvider? := some { firstTriggerCharacter := "}" }
  }
  match (fromJson? (toJson caps) : Except String ServerCapabilities) with
  | .ok c =>
    c.documentFormattingProvider?.isSome
      && c.documentRangeFormattingProvider?.isSome
      && c.documentOnTypeFormattingProvider?.map (·.firstTriggerCharacter) == some "}"
  | .error _ => false
