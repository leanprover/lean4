import Lean.Elab.GuardMsgs
import Lean.Elab.BuiltinEvalCommand
import Lean.Elab.DocString.Builtin

set_option doc.verso true
-- The test harness disables all linters on the command line; set the option explicitly so the
-- checks capture it enabled unless a `set_option ... in` turns it off at the docstring.
set_option linter.doc.deferred true

/-!
Tests that a forward reference in a module docstring is recorded against the module docstring rather
than a declaration, and run by the checker with the snippet's index. The reference
{name (scope := "Init")}`Nat.totallyMissingXYZ` does not resolve to a declaration.
-/

set_option linter.doc.deferred false in
/-!
A second module docstring is elaborated under `set_option linter.doc.deferred false in`, to check
for the option in the test.

A suppressed reference: {name (scope := "Init")}`Nat.alsoTotallyMissingXYZ` does not resolve either.
-/

set_option doc.verso false

open Lean Elab Term in
/--
info: FAIL module docstring #0: Unknown constant `Nat.totallyMissingXYZ`
---
info: FAIL module docstring #1: Unknown constant `Nat.alsoTotallyMissingXYZ`
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

open Lean Elab Term in
/--
info: FAIL module docstring #0: Unknown constant `Nat.totallyMissingXYZ`
-/
#guard_msgs in
#eval show TermElabM Unit from do
  let m := (← getEnv).mainModule
  let failures ← Lean.Doc.DeferredCheck.run (· == m)
    (shouldCheck := fun c =>
      return Linter.getLinterValue linter.doc.deferred (← c.options.toLinterOptions))
  if failures.isEmpty then
    logInfo "all deferred checks passed"
  else
    for (_, c, msg) in failures do
      let site := match c.site with
        | .decl n => toString n
        | .moduleDoc i => s!"module docstring #{i}"
      logInfo m!"FAIL {site}: {msg}"
