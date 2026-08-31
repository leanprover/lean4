/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.EnvExtension

namespace Lean

/--
Map from namespace name to (max) visibility of (any) defining module. Namespaces do not have
visibility of their own. We use this information to avoid redeclaring namespaces that would always
be provided by an import anyway.
-/
abbrev State := SMap Name Environment.Visibility

/--
Environment extension for tracking all `namespace` declared by users.
-/
private builtin_initialize namespacesExt : PersistentEnvExtension Name Name State ←
  registerPersistentEnvExtension {
    mkInitial       := pure {}
    addImportedFn   := fun as => do
      let env := (← read).env
      /-
      We compute a `HashMap` and then convert to `SMap` to improve Lean startup time.
      Note: we have used `perf` to profile Lean startup cost when processing a file containing just `import Lean`.
      6.18% of the runtime is here. It was 9.31% before the `HashMap` optimization.
      -/
      let capacity := as.foldl (init := 0) fun r e => r + e.size
      let mut map : Std.HashMap Name Environment.Visibility := Std.HashMap.emptyWithCapacity capacity
      for mod in env.header.modules, modEntries in as do
        let vis := if mod.isExported then .public else .private
        for e in modEntries do
          map := map.alter e fun
            | some .public => some .public
            | _            => some vis
      return SMap.fromHashMap map |>.switch
    -- local entries are not from private imports, so mark public
    addEntryFn      := fun s n => s.insert n .public
    exportEntriesFn s :=
      let entries := s.map₂.toArray.map (·.1)
      entries.qsort (·.quickLt)
    -- Namespaces from local helper constants can be disregarded in other environment branches. We
    -- do *not* want `getNamespaces` to have to wait on all prior branches.
    asyncMode       := .local
  }

namespace Environment

/-- Register a new namespace in the environment. -/
public def registerNamespace (env : Environment) (n : Name) : Environment :=
  -- Can only skip registering imported namespaces for public imports
  if namespacesExt.getState env |>.find? n |>.any (· == .public) then env else
    namespacesExt.addEntry env n

/-- Return `true` if `n` is the name of a namespace in `env`. -/
public def isNamespace (env : Environment) (n : Name) : Bool :=
  namespacesExt.getState env |>.contains n

/-- Returns an iterator over all namespaces in `env`. -/
public def getNamespaces (env : Environment) :=
  namespacesExt.getState env |>.iter.map (·.1)
