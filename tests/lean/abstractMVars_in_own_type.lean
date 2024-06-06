import Lean.Elab.Command

open Lean Meta

run_meta do
  let mvarid1 ← mkFreshExprMVar (.some (.sort 0))
  let mvarid2 ← mkFreshExprMVar (.some mvarid1)
  mvarid1.mvarId!.assign mvarid2 -- Now mvarid2 occurs in its own type
  -- does abstractMVars run into circles or is it fine?
  -- it used to cause a stack overflow, now it panics
  let r ← abstractMVars mvarid2 (levels := false)
  logInfo m!"{r.expr}"
