module

import Lean

/-! ## idbg syntax compiles in a do block -/

-- Verify the idbg syntax is accepted and type-checks.
-- We can't run this (the client loop would try to connect), just check elaboration.
-- Disable inServer so the elaborator doesn't block waiting for TCP connection
set_option Elab.inServer false in
set_option backward.do.legacy false in
def idbgTypeCheck (x : Nat) (s : String) : IO Unit := do
  idbg x + s.length

/-! ## Running idbgClientLoop doesn't cause a segfault -/

-- Note: while running it once didn't consistently cause a segfault, running it twice did

#guard_msgs (drop error) in
#eval Lean.Idbg.idbgClientLoop "hi" #[`Nonexistent, `Nonexistent] id

#guard_msgs (drop error) in
#eval Lean.Idbg.idbgClientLoop "hi" #[`Nonexistent, `Nonexistent] id
