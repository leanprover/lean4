import Lean.Elab.GuardMsgs
import Lean.Elab.BuiltinEvalCommand
import Lean.Elab.DocString.Builtin

set_option doc.verso true

/-!
Tests that a forward reference in a module docstring is recorded against the module docstring rather
than a declaration, and run by the checker with the snippet's index. The reference
{name (scope := "Init")}`Nat.totallyMissingXYZ` does not resolve to a declaration.
-/

set_option doc.verso false

open Lean Elab Term in
/--
info: FAIL module docstring #0: Unknown constant `Nat.totallyMissingXYZ`
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
