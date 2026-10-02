import TrackedExt.Ext

/-!
Generation-tracked environment extensions (`PersistentEnvExtensionDescrCore.trackGen`): every
modification bumps the extension's own generation and `Environment.trackedGen`, except with
`bumpGen := false`; modifications of untracked extensions bump neither; an earlier environment keeps
its generations; and tracked extensions cannot use `AsyncMode.sync`.
-/

open Lean

/--
info: state 2, generation +1, other tracked +0, trackedGen +1
---
info: second tracked: generation +1, first tracked +0, trackedGen +1
---
info: untracked: trackedGen +0
---
info: earlier environment: state 0, generation +0
-/
#guard_msgs in
#eval show CoreM Unit from do
  let env ← getEnv
  let gen := trackedExt.getGen env
  let gen₂ := trackedExt₂.getGen env
  let env₁ := trackedExt.modifyState env (· + 1)
  let env₂ := trackedExt.modifyState env₁ (· + 1) (bumpGen := false)
  logInfo m!"state {trackedExt.getState env₂}, generation +{trackedExt.getGen env₂ - gen}, \
    other tracked +{trackedExt₂.getGen env₂ - gen₂}, trackedGen +{env₂.trackedGen - env.trackedGen}"
  let env₃ := trackedExt₂.modifyState env₂ (· + 1)
  logInfo m!"second tracked: generation +{trackedExt₂.getGen env₃ - gen₂}, \
    first tracked +{trackedExt.getGen env₃ - trackedExt.getGen env₂}, \
    trackedGen +{env₃.trackedGen - env₂.trackedGen}"
  let env₄ := untrackedExt.modifyState env₃ (· + 1)
  logInfo m!"untracked: trackedGen +{env₄.trackedGen - env₃.trackedGen}"
  logInfo m!"earlier environment: state {trackedExt.getState env}, \
    generation +{trackedExt.getGen env - gen}"

/-- info: true -/
#guard_msgs in
#eval syncTrackedRejected
