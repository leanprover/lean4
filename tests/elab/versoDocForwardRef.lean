import Lean.Elab.GuardMsgs
import Lean.Elab.BuiltinEvalCommand
import Lean.Elab.DocString.Builtin

/-!
Tests that forward references in Verso docstrings record deferred checks, and that the checker
runs them: a reference to an existing name passes, a reference to a missing name fails, both
located at the referring declaration.
-/

set_option doc.verso true

/-- A reference to {name (scope := "Init")}`Nat.succ`. -/
def good := 1

/-- A reference to {name (scope := "Init")}`Nat.doesNotExistXYZ`. -/
def bad := 2

open Lean Elab Term in
/--
info: FAIL bad: Unknown constant `Nat.doesNotExistXYZ`
-/
#guard_msgs in
#eval show TermElabM Unit from do
  let m := (← getEnv).mainModule
  let failures ← Lean.Doc.DeferredCheck.run (· == m)
  if failures.isEmpty then
    logInfo "all deferred checks passed"
  else
    for (_, c, msg) in failures do
      let site := match c.site with
        | .decl n => toString n
        | .moduleDoc i => s!"module docstring #{i}"
      logInfo m!"FAIL {site}: {msg}"
