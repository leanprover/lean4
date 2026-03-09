import Lean


-- This should not be swallowed by the `try`
/--
warning: Possibly looping simp theorem: `← Nat.add_zero 1`

Hint: You can disable a simp theorem from the default simp set by passing `- theoremName` to `simp`.
---
error: Tactic `simp` failed with a nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
set_option maxRecDepth 200 in-- low to make this fast
example : 1 = sorry := by
  try simp [← Nat.add_zero 1]

open Lean

/--
error: Tactic `foo` failed with a nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
run_meta show MetaM Unit from do
  try
    -- Throw a recursion depth error wrapped in a nested error
    tryCatchRuntimeEx
      (throwMaxRecDepthAt .missing)
      (fun e =>
        Meta.throwNestedTacticEx `foo e)
  catch e =>
    -- We didn't use `tryCatchRuntimeEx` here so we shouldn't catch it.
    throwError m!"Should not be caught"
