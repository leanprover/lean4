/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Environment

namespace Lean

/--
Environment extension for tracking all `namespace` declared by users.
-/
builtin_initialize namespacesExt : SimplePersistentEnvExtension Name NameSSet ←
  registerSimplePersistentEnvExtension {
    addImportedFn   := fun as =>
      /-
      We compute a `HashMap Name Unit` and then convert to `NameSSet` to improve Lean startup time.
      Note: we have used `perf` to profile Lean startup cost when processing a file containing just `import Lean`.
      6.18% of the runtime is here. It was 9.31% before the `HashMap` optimization.
      -/
      let capacity := as.foldl (init := 0) fun r e => r + e.size
      let map : Std.HashMap Name Unit := Std.HashMap.empty capacity
      let map := mkStateFromImportedEntries (fun map name => map.insert name ()) map as
      SMap.fromHashMap map |>.switch
    addEntryFn      := fun s n => s.insert n
    -- Namespaces from local helper constants can be disregarded in other environment branches. We
    -- do *not* want `getNamespaceSet` to have to wait on all prior branches.
    asyncMode       := .local
  }

namespace Environment

/-- Register a new namespace in the environment. -/
def registerNamespace (env : Environment) (n : Name) : Environment :=
  if (namespacesExt.getState env).contains n then env else namespacesExt.addEntry env n

/-- Return `true` if `n` is the name of a namespace in `env`. -/
def isNamespace (env : Environment) (n : Name) : Bool :=
  (namespacesExt.getState env).contains n

/-- Return a set containing all namespaces in `env`. -/
def getNamespaceSet (env : Environment) : NameSSet :=
  namespacesExt.getState env
