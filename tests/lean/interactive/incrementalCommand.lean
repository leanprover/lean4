/-!
Comments after a command may become part of the next command on edits.
(Note that this module doc is a command on its own)
-/

--v sync
--v insert: "-"
/-
info: "3.14"
-/
#guard_msgs in
#eval "3.14"
--^ collectDiagnostics
-- (should be empty if edit was handled correctly)

/-! Same, after header -/
-- RESET
import Init

--v sync
--v insert: "-"
/-
info: "3.14"
-/
#guard_msgs in
#eval "3.14"
--^ collectDiagnostics
-- (should be empty if edit was handled correctly)

/-! Commands not marked as `[incremental]` should not allow accidental reuse in unknown contexts. -/
-- RESET
import Lean

open Lean Elab Command in
elab "wrap" num c:command : command => do
  elabCommand c

   --v change: "1" "2"
wrap 1 def wrapped := by
  dbg_trace "w"
