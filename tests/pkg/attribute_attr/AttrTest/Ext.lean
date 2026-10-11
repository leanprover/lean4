import Lean

/-! Defines the env extension only.  No attribute here. -/

open Lean

initialize markedExt : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := Array.push
    addImportedFn := fun ess => ess.foldl (init := #[]) Array.append
  }

def getMarked (env : Environment) : Array Name :=
  markedExt.getState env
