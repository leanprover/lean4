import TrackedExt.Ext

/-!
Generation-tracked environment extensions (`PersistentEnvExtensionDescrCore.trackGen`): every
modification bumps `Environment.trackedGen`, except with `bumpGen := false`; modifications of
untracked extensions do not; an earlier environment keeps its value; and tracked extensions cannot
use `AsyncMode.sync`.
-/

open Lean

/--
info: state 2, trackedGen +1
---
info: second tracked: trackedGen +1
---
info: untracked: trackedGen +0
---
info: earlier environment: state 0, trackedGen +0
-/
#guard_msgs in
#eval show CoreM Unit from do
  let env ← getEnv
  let gen := env.trackedGen
  let env₁ := trackedExt.modifyState env (· + 1)
  let env₂ := trackedExt.modifyState env₁ (· + 1) (bumpGen := false)
  logInfo m!"state {trackedExt.getState env₂}, trackedGen +{env₂.trackedGen - gen}"
  let env₃ := trackedExt₂.modifyState env₂ (· + 1)
  logInfo m!"second tracked: trackedGen +{env₃.trackedGen - env₂.trackedGen}"
  let env₄ := untrackedExt.modifyState env₃ (· + 1)
  logInfo m!"untracked: trackedGen +{env₄.trackedGen - env₃.trackedGen}"
  logInfo m!"earlier environment: state {trackedExt.getState env}, \
    trackedGen +{env.trackedGen - gen}"

/-- info: true -/
#guard_msgs in
#eval syncTrackedRejected
