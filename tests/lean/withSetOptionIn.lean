import Lean

/-!
# `withSetOptionIn`

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

/-- info: [debug] foo -/
#guard_msgs in
set_option trace.debug true in #trace_debug_foo

/-! ## Test

Should trace `[debug] foo`, and not log the error "unexpected command 'in'".
-/

/-- info: [debug] foo -/
#guard_msgs in
#test set_option trace.debug true in #trace_debug_foo
