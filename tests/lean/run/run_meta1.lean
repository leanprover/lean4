import Lean.Elab.Command

run_meta guard true

open Lean Meta in
/-- info: Bool -/
#guard_msgs in
run_meta do
  let type ← inferType (mkConst ``true)
  logInfo type
