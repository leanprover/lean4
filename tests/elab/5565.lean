import Lean.Elab.Command

run_meta do
  Lean.tryCatchRuntimeEx
    (do
      Lean.Core.throwMaxHeartbeat `foo `bar 200)
    (fun e =>
      unless e.isMaxHeartbeat do
        throwError "Not a max heartbeat error:{Lean.indentD e.toMessageData}")
