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

When a module is exported, `build` summarizes the global entries it exports at each olean level; the
summaries are stored by a separate persistent extension. On import, `addImported` adds the global
entries of all imported modules to the initial state, given in module order with their summaries if
they have global entries. If some imported module with global entries has no summary, e.g. because
an older stage exported it during bootstrapping, the entries are added one by one instead: building
missing summaries would be more expensive, and mixing both would change the order of entries.
-/
public def registerSimpleScopedEnvExtensionWithIndex {ι : Type}
    (descr : SimpleScopedEnvExtension.Descr α σ) (build : Environment → Array α → ι)
    (addImported : σ → Array (Option ι × Array (Entry α)) → ImportM σ) :
    IO (SimpleScopedEnvExtension α σ) := do
  -- the summary extension needs the main extension and vice versa
  let indexRef : IO.Ref (Option (PersistentEnvExtension ι Unit Unit)) ← IO.mkRef none
  let ext ← registerSimpleScopedEnvExtension { descr with
    addImportedGlobals? := some fun s as => do
      let some indexExt ← indexRef.get | return none
      let env := (← read).env
      let mods := as.mapIdx fun i a => ((indexExt.getModuleEntries env (i : ModuleIdx))[0]?, a)
      if mods.all fun (summary?, a) => summary?.isSome || !a.any (· matches .global _) then
        return some (← addImported s mods)
      else
        return none }
  let indexExt : PersistentEnvExtension ι Unit Unit ← registerPersistentEnvExtension {
    name := descr.name ++ `moduleIndex
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
  indexRef.set indexExt
  return ext

end Lean
