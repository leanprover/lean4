/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.CoreM
public import Lean.Compiler.MetaAttr  -- TODO: public because of specializations

/-!
Infrastructure for recording extra import dependencies not implied by the environment constants for
the benefit of `shake`.
-/

namespace Lean

/-- Additional import dependency for elaboration. -/
public structure ExtraModUse where
  /-- Dependency's module name. -/
  module : Name
  /-- Whether dependency must be imported as `public`. -/
  isExported : Bool
  /-- Whether dependency must be imported as `meta`. -/
  isMeta : Bool
deriving BEq, Hashable, Repr

builtin_initialize extraModUses : SimplePersistentEnvExtension ExtraModUse (PHashSet ExtraModUse) ←
  registerSimplePersistentEnvExtension {
    addEntryFn m k := m.insert k
    addImportedFn _ := {}
    exportEntriesFnEx? := some fun _ _ entries => fun
      | .private => entries.toArray
      | _        => #[]
    asyncMode := .sync
    replay? := some <| SimplePersistentEnvExtension.replayOfFilter (·.contains ·) (·.insert ·)
  }

/-- Returns additional recorded import dependencies of the given module. -/
public def getExtraModUses (env : Environment) (modIdx : ModuleIdx) : Array ExtraModUse :=
  extraModUses.getModuleEntries env modIdx

/-- Copies additional recorded import dependencies from one environment to another. -/
public def copyExtraModUses (src dest : Environment) : Environment := Id.run do
  let mut env := dest
  for entry in extraModUses.getEntries src do
    if !(extraModUses.getState (asyncMode := .local) env).contains entry then
      env := extraModUses.addEntry env entry
  env

variable [Monad m] [MonadEnv m] [MonadTrace m] [MonadOptions m] [MonadRef m] [AddMessageContext m]

def recordExtraModUseCore (mod : Name) (isMeta : Bool) (hint : Name := .anonymous) : m Unit := do
  let entry := { module := mod, isExported := (← getEnv).isExporting, isMeta }
  if !(extraModUses.getState (asyncMode := .local) (← getEnv)).contains entry then
    trace[extraModUses] "recording {if entry.isExported then "public" else "private"} \
      {if isMeta then "meta" else "regular"} extra mod use {mod}\
      {if hint.isAnonymous then m!"" else m!" of {hint}"}"
    modifyEnv (extraModUses.addEntry · entry)

/--
Records an additional import dependency for the current module, using `Environment.isExporting` as
the visibility level.
-/
public def recordExtraModUse (modName : Name) (isMeta : Bool) : m Unit := do
  if modName != (← getEnv).mainModule then
    recordExtraModUseCore modName isMeta

/--
Records the module of the given declaration as an additional import dependency for the current
module, using `Environment.isExporting` as the visibility level. If the declaration itself is
already `meta`, the module dependency is recorded as a non-`meta` dependency.
-/
public def recordExtraModUseFromDecl (declName : Name) (isMeta : Bool) : m Unit := do
  let env ← getEnv
  if let some mod := env.getModuleIdxFor? declName |>.bind (env.header.modules[·]?) then
    -- If the declaration itself is already `meta`, no need to mark the import.
    let isMeta := isMeta && !Lean.isMeta (← getEnv) declName
    recordExtraModUseCore mod.module isMeta (hint := declName)

builtin_initialize isExtraRevModUseExt : SimplePersistentEnvExtension Unit Unit ←
  registerSimplePersistentEnvExtension {
    addEntryFn s e := ()
    addImportedFn _ := ()
    asyncMode := .sync
  }

/-- Checks whether this module should be preserved as an import by `shake`. -/
public def isExtraRevModUse (env : Environment) (modIdx : ModuleIdx) : Bool :=
  !(isExtraRevModUseExt.getModuleEntries env modIdx |>.isEmpty)

/-- Records this module to be preserved as an import by `shake`. -/
public def recordExtraRevUseOfCurrentModule : m Unit := do
  if isExtraRevModUseExt.getEntries (asyncMode := .local) (← getEnv) |>.isEmpty then
    modifyEnv (isExtraRevModUseExt.addEntry · ())

builtin_initialize
  registerTraceClass `extraModUses
