/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.ScopedEnvExtension

namespace Lean

open ScopedEnvExtension

/--
Registers a simple scoped environment extension (see `registerSimpleScopedEnvExtension`) whose
imported global entries are added using per-module summaries instead of one by one.

When a module is exported, `build` summarizes the global entries it exports at each olean level, if
any; the summaries are stored by a separate persistent extension. On import, `addImported` adds the
global entries of all imported modules to the initial state, given in module order, each with its
entries and its summary (`none` for modules without global entries).
-/
public def registerSimpleScopedEnvExtensionWithSummaries {ι : Type}
    (descr : SimpleScopedEnvExtension.Descr α σ) (build : Environment → Array α → ι)
    (addImported : σ → Array (Option ι × Array (Entry α)) → ImportM σ) :
    IO (SimpleScopedEnvExtension α σ) := do
  let summaryName := descr.name ++ `moduleSummary
  let ext ← registerSimpleScopedEnvExtension { descr with
    importGlobals := fun as => do
      -- Looked up by name, as referencing the summary extension from here would create a cycle
      -- through the export function below, which the compactor cannot save (e.g. in
      -- `--incr-header-save` snapshots).
      let some summaryExt := (← persistentEnvExtensionsRef.get).find? (·.name == summaryName)
        | throw <| .userError s!"summary extension '{summaryName}' is not registered"
      let env := (← read).env
      addImported descr.initial <| as.mapIdx fun i a =>
        let summary? : Option EnvExtensionEntry :=
          (summaryExt.getModuleEntries env (i : ModuleIdx))[0]?
        ((unsafe unsafeCast summary? : Option ι), a) }
  let _ : PersistentEnvExtension ι Unit Unit ← registerPersistentEnvExtension {
    name := summaryName
    mkInitial := pure ()
    addImportedFn := fun _ => pure ()
    addEntryFn := fun s _ => s
    exportEntriesFnEx := fun env _ =>
      let es := exportEntriesFn ext.descr env (ext.ext.getState env)
      let summarize (es : Array (Entry α)) :=
        let globals := es.filterMap fun | .global e => some e | _ => none
        if globals.isEmpty then #[] else #[build env globals]
      { exported := summarize es.exported, server := summarize es.server
        «private» := summarize es.private }
  }
  return ext

end Lean
