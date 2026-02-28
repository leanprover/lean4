import Lean.Data.Lsp.Basic
import Lean.Data.Lsp.Capabilities
import Lean.Server.Utils

/-!
# LSP `$/progress` notification helpers

Validates JSON serialization of `WorkDoneProgressBegin`, `WorkDoneProgressReport`,
`WorkDoneProgressEnd`, `WorkDoneProgressCreateParams`, and capability parsing.
-/

open Lean Lsp Server

/-! ## WorkDoneProgressBegin serializes `kind` as `"begin"` -/

/--
info: {"title": "Lake",
 "message": "Setting up...",
 "kind": "begin",
 "cancellable": false}
-/
#guard_msgs in
  #eval do
    let begin_ : WorkDoneProgressBegin := { title := "Lake", message? := some "Setting up..." }
    IO.println (toString (toJson begin_))

/-! ## WorkDoneProgressReport serializes `kind` as `"report"` -/

/--
info: {"message": "Building Mathlib.Algebra", "kind": "report", "cancellable": false}
-/
#guard_msgs in
  #eval do
    let report : WorkDoneProgressReport := { message? := some "Building Mathlib.Algebra" }
    IO.println (toString (toJson report))

/-! ## WorkDoneProgressEnd serializes `kind` as `"end"` -/

/--
info: {"kind": "end"}
-/
#guard_msgs in
  #eval do
    let end_ : WorkDoneProgressEnd := {}
    IO.println (toString (toJson end_))

/-! ## WorkDoneProgressCreateParams round-trips through JSON -/

/--
info: {"token": "myToken"}
-/
#guard_msgs in
  #eval do
    let params : WorkDoneProgressCreateParams := { token := "myToken" }
    IO.println (toString (toJson params))

/-! ## ProgressParams wraps value with token -/

/--
info: {"value": {"title": "Lake", "kind": "begin", "cancellable": false},
 "token": "lake"}
-/
#guard_msgs in
  #eval do
    let notif := mkProgressBeginNotification "lake" "Lake"
    IO.println (toString (toJson notif.param))

/-! ## ClientCapabilities.workDoneProgress accessor -/

/--
info: true
-/
#guard_msgs in
  #eval do
    let caps : ClientCapabilities := {
      window? := some { workDoneProgress? := some true }
    }
    IO.println (toString caps.workDoneProgress)

/--
info: false
-/
#guard_msgs in
  #eval do
    let caps : ClientCapabilities := {}
    IO.println (toString caps.workDoneProgress)

/--
info: false
-/
#guard_msgs in
  #eval do
    let caps : ClientCapabilities := {
      window? := some {}
    }
    IO.println (toString caps.workDoneProgress)

/-! ## ClientCapabilities with workDoneProgress round-trips through JSON -/

/--
info: true
-/
#guard_msgs in
  #eval do
    let j := toJson ({ window? := some { workDoneProgress? := some true } } : ClientCapabilities)
    match fromJson? j with
    | .ok (caps : ClientCapabilities) => IO.println (toString caps.workDoneProgress)
    | .error e => IO.println s!"parse error: {e}"

/-! ## lakeProgressToken is the expected string -/

/--
info: "lean4/lakeSetup"
-/
#guard_msgs in
  #eval IO.println (toString (toJson lakeProgressToken))

/-! ## mkWorkDoneProgressCreateRequest produces correct request -/

/--
info: window/workDoneProgress/create
-/
#guard_msgs in
  #eval do
    let req := mkWorkDoneProgressCreateRequest 42 lakeProgressToken
    IO.println req.method

/--
info: {"token": "lean4/lakeSetup"}
-/
#guard_msgs in
  #eval do
    let req := mkWorkDoneProgressCreateRequest 42 lakeProgressToken
    IO.println (toString (toJson req.param))
