import Lean

open Lean

initialize trackedExt : EnvExtension Nat ←
  registerEnvExtension (pure 0) (name := `trackedExt) (trackGen := true)

initialize trackedExt₂ : EnvExtension Nat ←
  registerEnvExtension (pure 0) (name := `trackedExt₂) (trackGen := true)

initialize untrackedExt : EnvExtension Nat ←
  registerEnvExtension (pure 0) (name := `untrackedExt)

/-- Whether registering a generation-tracked extension with `AsyncMode.sync` was rejected. -/
initialize syncTrackedRejected : Bool ←
  try
    discard <| registerEnvExtension (pure 0) (asyncMode := .sync) (trackGen := true)
    pure false
  catch _ =>
    pure true
