import Lean

/-!
# `withSetOptionIn`
-/

section recurse

/-!
This test checks that `withSetOptionIn` recurses into the command syntax (`stx[2]`) in
`set_option ... in <cmd>`.

Prior to #3806, `withSetOptionIn` erroneously recursed into the syntax `in` (`stx[1]`).
-/

open Lean Elab Command

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

open Lean Elab Command

/-- Two persistent arrays are equal if the corresponding elements are equal. -/
def Lean.PersistentArray.eqOf [Inhabited α] (a b : PersistentArray α) (eq : α → α → Bool) : Bool :=
  a.size == b.size && Id.run do
    for i in 0...a.size do
      unless eq a[i]! b[i]! do return false
    return true

/-- Compare the structure of an infotree. (Do not check that the infos are the same.) -/
partial def Lean.Elab.InfoTree.structEq : InfoTree → InfoTree → Bool
  | .context _ t, .context _ t' => t.structEq t'
  | .node _ ts, .node _ ts' => ts.eqOf ts' structEq
  | .hole _, .hole _ => true
  | _, _ => false

/-- Collect the option names from all `OptionInfo` infos in the infotrees. -/
def getOptionNames (ts : PersistentArray InfoTree) : List Name :=
  ts.foldl (init := []) fun acc t =>
    acc ++ t.collectNodesBottomUp fun
      | _, .ofOptionInfo i, _, ns => i.optionName :: ns
      | _, _, _, ns => ns

def compareWithSetOptionIn : CommandElab := fun stx => do
  let originalTrees ← getInfoTrees
  logInfo m!"without `withSetOptionIn`:\n\
    - `linter.all := {← getBoolOption `linter.all}`\n\
    - Found option names in trees: {getOptionNames (← getInfoTrees)}"
  let runWithSetOptionIn : CommandElab := withSetOptionIn fun _ => do
    logInfo m!"trees are structurally equal: {originalTrees.eqOf (← getInfoTrees) (·.structEq ·)}"
    logInfo m!"with `withSetOptionIn`:\n\
      - `linter.all := {← getBoolOption `linter.all}`\n\
      - Found option names in trees: {getOptionNames (← getInfoTrees)}"
  runWithSetOptionIn stx

/-
Should show `linter.all := false` without `withSetOptionIn`, and `linter.all := true` with.
Should find the option name `linter.all` exactly once **both** with and without `withSetOptionIn`.
This ensures that we're looking at correct post-elaboration infotrees in this test.
-/

/--
info: without `withSetOptionIn`:
- `linter.all := false`
- Found option names in trees: [linter.all]
---
info: trees are structurally equal: true
---
info: with `withSetOptionIn`:
- `linter.all := true`
- Found option names in trees: [linter.all]
-/
#guard_msgs in
run_cmd do
  let stx ← `(command| set_option linter.all true in example : True := trivial)
  elabCommand stx
  compareWithSetOptionIn stx

/-
Should have `linter.all := false` both times, since the value is malformed, but still find an
`OptionInfo`.

Should only log the `set_option` error **once** from `elabCommand`. `compareWithSetOption` should
not produce an error.
-/

/--
error: set_option value type mismatch: The value
  3
has type
  Nat
but the option `linter.all` expects a value of type
  Bool
---
info: without `withSetOptionIn`:
- `linter.all := false`
- Found option names in trees: [linter.all]
---
info: trees are structurally equal: true
---
info: with `withSetOptionIn`:
- `linter.all := false`
- Found option names in trees: [linter.all]
-/
#guard_msgs in
run_cmd do
  let stx ← `(command| set_option linter.all 3 in example : True := trivial)
  elabCommand stx
  try compareWithSetOptionIn stx catch ex =>
    throwError "comparison produced error:\n\n{ex.toMessageData}"

end infotree

section malformedOption

/-! A malformed `set_option` should only produce an error at the command level;
linters should ignore the bad option and not fail. -/

-- Control: ensure `linter.missingDocs` is present and uses `withSetOptionIn`

set_option linter.missingDocs false

/--
warning: missing doc string for public def foo

Note: This linter can be disabled with `set_option linter.missingDocs false`
-/
#guard_msgs in
set_option linter.missingDocs true in
def foo := true

-- No error from `linter.missingDocs` on unknown options
/--
error: Unknown option `unknown.option`
-/
#guard_msgs in
set_option unknown.option true in
example := trivial

-- No error from `linter.missingDocs` on bad option values
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
