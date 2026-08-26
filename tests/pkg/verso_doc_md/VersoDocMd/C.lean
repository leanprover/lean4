module

import Lean.DocString
import Lean.Meta.Basic
public import VersoDocMd.B

public section

/-!
Renders `Bar`'s docstring (module `B`), whose custom element includes `Foo`'s docstring (module
`A`) using the renderer registered in module `Defs`. The renderer and its target are reached across
module boundaries at render time.
-/

/-- info: Included: Hello from Foo across modules. -/
#guard_msgs in
open Lean in
run_meta do
  let env ← getEnv
  let some r ← Lean.findDocString? env `Bar | failure
  let expected := "Included: Hello from Foo across modules."
  unless r.startsWith expected do throwError m!"unexpected render: {repr r}"
  logInfo expected
