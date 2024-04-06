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

/-! ## Controls -/

#trace_debug_foo -- no trace

set_option trace.debug true in #trace_debug_foo -- trace

/-! ## Test

Should trace `[debug] foo`, and not log the error "unexpected command 'in'".
-/

#test set_option trace.debug true in #trace_debug_foo
