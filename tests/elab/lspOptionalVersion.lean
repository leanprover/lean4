import Lean.Data.Lsp.Basic

open Lean Lsp

/-!
`VersionedTextDocumentIdentifier` serializes `version := none` as `"version": null`, since LSP's
`OptionalVersionedTextDocumentIdentifier` requires the field.
-/

/-- info: {"version": null, "uri": "file:///a.lean"} -/
#guard_msgs in
#eval toJson ({ uri := "file:///a.lean" } : VersionedTextDocumentIdentifier)

/-- info: {"version": 3, "uri": "file:///a.lean"} -/
#guard_msgs in
#eval toJson ({ uri := "file:///a.lean", version := some 3 } : VersionedTextDocumentIdentifier)

/-! A `TextDocumentEdit` for a document whose version is unknown, e.g. one being created. -/

/--
info: {"documentChanges":
 [{"textDocument": {"version": null, "uri": "file:///a.lean"},
   "edits":
   [{"range":
     {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 0}},
     "newText": "x"}]}]}
-/
#guard_msgs in
#eval toJson <| WorkspaceEdit.ofTextEdit { uri := "file:///a.lean" }
  { range := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, newText := "x" }

/-! Deserialization accepts a missing `version`, `null` and a number. -/

/-- info: [Except.ok none, Except.ok none, Except.ok (some 3)] -/
#guard_msgs in
#eval [r#"{"uri": "u"}"#, r#"{"uri": "u", "version": null}"#, r#"{"uri": "u", "version": 3}"#].map
  fun s => (Json.parse s >>= fromJson? (α := VersionedTextDocumentIdentifier)).map (·.version)

/-! `fromJson?` inverts `toJson`, also inside a `WorkspaceEdit`. -/

/-- info: [true, true] -/
#guard_msgs in
#eval ([{ uri := "file:///a.lean" }, { uri := "file:///a.lean", version := some 3 }] :
    List VersionedTextDocumentIdentifier).map fun i =>
  match fromJson? (α := VersionedTextDocumentIdentifier) (toJson i) with
  | .ok j => j.uri == i.uri && j.version == i.version
  | .error _ => false

/-- info: true -/
#guard_msgs in
#eval
  let e := WorkspaceEdit.ofTextEdit { uri := "file:///a.lean" }
    { range := ⟨⟨0, 0⟩, ⟨0, 0⟩⟩, newText := "x" }
  match fromJson? (α := WorkspaceEdit) (toJson e) with
  | .ok e' => toJson e' == toJson e
  | .error _ => false
