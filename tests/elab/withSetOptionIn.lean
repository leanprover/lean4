import Lean

/-!
# `withSetOptionIn`
-/

open Lean Elab Command

section recurse

/-!
This test checks that `withSetOptionIn` recurses into the command syntax (`stx[2]`) in
`set_option ... in <cmd>`.

Prior to #3806, `withSetOptionIn` erroneously recursed into the syntax `in` (`stx[1]`).
-/

/-- Trace `foo` when `set_option trace.debug true`. -/
elab "#trace_debug_foo" : command => do trace[debug] "foo"

/-- Elab `cmd` using `withSetOptionIn`. -/
elab "#test " cmd:command : command => withSetOptionIn elabCommand cmd

/-! ## Controls

Ensure that `#trace_debug_foo` works as expected.
-/

#guard_msgs in
#trace_debug_foo

/-- trace: [debug] foo -/
#guard_msgs(trace) in
set_option trace.debug true in #trace_debug_foo

/-! ## Test

Should trace `[debug] foo`, and not log the error "unexpected command 'in'".
-/

/-- trace: [debug] foo -/
#guard_msgs(trace) in
#test set_option trace.debug true in #trace_debug_foo

end recurse

section infotree

/-!
These tests check that `withSetOptionIn` does not modify the infotrees (#11313).

Modifying the infotrees in `withSetOptionIn` in linters created context-free info nodes, which
caused `visitM` and related means of searching the infotrees, such as `collectNodesBottomUp`, to
panic.

We also check that we do not error inside linters due to malformed options.
-/

/-- The total size of an infotree plus `acc`. -/
partial def sizeAux (acc : Nat) : InfoTree → Nat
  | .node _ ch => ch.foldl (init := acc + 1) sizeAux
  | .context _ t => sizeAux (acc + 1) t
  | .hole _ => acc + 1

/-- Check that the infotrees within `withSetOptionIn` all have a context and match the size of the
infotrees before `withSetOptionIn`. Noisy for confirmation when `pp.all` is true via
`set_option ... in`. -/
def checkInfoTrees : Linter where run cmd := do
  -- Get initial infotree size
  let initInfoTreeSize := (← getInfoTrees).foldl (init := 0) sizeAux
  if getPPAll (← getOptions) then throwError "`pp.all` should not be set ambiently for testing."
  withSetOptionIn (fun cmd => do
    if getPPAll (← getOptions) then logInfo m!"Test linter is functioning."
    -- Ensure we're checking something.
    if (← getInfoTrees).isEmpty then throwError "No infotrees."
    -- Ensure every infotree has context
    unless (← getInfoTrees).all (· matches .context ..) do
      logError "Context-free infotree!"
    -- Ensure the number of nodes is the same
    unless initInfoTreeSize = (← getInfoTrees).foldl (init := 0) sizeAux do
      logError "Wrong size!") cmd

run_cmd do addLinter checkInfoTrees

-- This errored with both "Context-free infotree!" and "Wrong size!" prior to #11313.
/--
info: Test linter is functioning.
-/
#guard_msgs in
set_option pp.all true in
example : True := trivial

end infotree

section malformedOption

/-! A malformed `set_option` should only produce an error at the command level;
linters should ignore the bad option and not fail. -/

-- Control: ensure `linter.indexVariables` is present and uses `withSetOptionIn`

set_option linter.indexVariables false

/--
warning: Forbidden variable appearing as an index: use `i`, `j`, or `k`: x

Note: This linter can be disabled with `set_option linter.indexVariables false`
-/
#guard_msgs in
set_option linter.indexVariables true in
example (a : List Bool) (x : Nat) := a[x]?

-- No error from `linter.indexVariables` on unknown options
/--
error: Unknown option `unknown.option`
-/
#guard_msgs in
set_option unknown.option true in
example := trivial

-- No error from `linter.indexVariables` on bad option values
/--
error: set_option value type mismatch: The value
  3
has type
  Nat
but the option `linter.all` expects a value of type
  Bool
-/
#guard_msgs in
set_option linter.all 3 in
example := trivial

end malformedOption
