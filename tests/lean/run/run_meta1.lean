import Lean.Elab.Command

run_meta guard true

open Lean Meta in
run_meta do
  let type ← inferType (mkConst ``true)
  IO.println type
