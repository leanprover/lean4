/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.MonadEnv

namespace Lean

namespace CollectAxioms

structure State where
  /--
  Cache mapping constants walked by this run to their (sorted) axiom dependencies. Constants
  answered by `extFind?` are deliberately not copied into this layer, so it contains exactly the
  constants whose dependencies were not already recorded elsewhere.
  -/
  seen   : NameMap (Array Name) := {}
  /-- Axioms accumulated for the current constant being processed. -/
  axioms : NameSet := {}

abbrev M := ReaderT Environment $ StateM State

def runM (env : Environment) (x : M α) : α :=
  x.run env |>.run' {}

private def insertArray (s : NameSet) (axs : Array Name) : NameSet :=
  axs.foldl (init := s) fun acc ax => acc.insert ax

/--
Collect axioms reachable from constant `c`, using `extFind?` to look up pre-computed axioms
for imported and already-recorded declarations. Results for walked constants are cached in
`State.seen`, the second layer of the cache on top of `extFind?`.

When processing a constant not found in `extFind?` or the cache, the function temporarily
clears the axiom accumulator, recurses into the constant's dependencies, caches the result
in `seen`, and merges the collected axioms back.
-/
private partial def collect
    (extFind? : Environment → Name → Option (Array Name))
    (c : Name) : M Unit := do
  let env ← read
  -- Check extension for pre-computed axioms (imported and already-recorded declarations)
  if let some axs := extFind? env c then
    modify fun s => { s with axioms := insertArray s.axioms axs }
    return
  -- Check local cache
  let s ← get
  if let some axs := s.seen.find? c then
    modify fun s => { s with axioms := insertArray s.axioms axs }
    return
  -- Recurse: temporarily clear axioms to isolate this constant's contribution.
  -- Insert sentinel to prevent infinite recursion (e.g., inductives ↔ constructors).
  let savedAxioms := s.axioms
  modify fun s => { s with axioms := {}, seen := s.seen.insert c #[] }
  let collectExpr (e : Expr) : M Unit := e.getUsedConstants.forM (collect extFind?)
  -- Take constants from the kernel env, which may differ from the elab env for (async) errors.
  match env.checked.get.find? c with
  | some (.axiomInfo v)  =>
      modify fun s => { s with axioms := s.axioms.insert c }
      collectExpr v.type
  | some (.defnInfo v)   => collectExpr v.type *> collectExpr v.value
  | some (.thmInfo v)    => collectExpr v.type *> collectExpr v.value
  | some (.opaqueInfo v) => collectExpr v.type *> collectExpr v.value
  | some (.quotInfo _)   => pure ()
  | some (.ctorInfo v)   => collectExpr v.type
  | some (.recInfo v)    => collectExpr v.type
  | some (.inductInfo v) => collectExpr v.type *> v.ctors.forM (collect extFind?)
  | none                 => pure ()
  -- Cache result (sorted for canonical order) and merge back into saved axioms
  let collected := (← get).axioms
  let result := collected.toArray.qsort Name.lt
  modify fun s => { s with
    seen   := s.seen.insert c result
    axioms := insertArray savedAxioms result
  }

/-- Collect axioms for `c` and return its sorted axiom list from the cache. -/
private def collectAndGet
    (extFind? : Environment → Name → Option (Array Name))
    (c : Name) : M (Array Name) := do
  if let some axs := extFind? (← read) c then
    return axs
  collect extFind? c
  let some axs := (← get).seen.find? c | panic! s!"collectAndGet: '{c}' not in seen after collect"
  return axs

end CollectAxioms

/--
Extension state holding imported module entries for efficient lookup of
pre-computed axiom data.

We use `registerPersistentEnvExtension` with manual lookup instead of `MapDeclarationExtension`
because `exportEntriesFnEx` needs to call `collect`, which needs the extension's `find?`, but
`exportEntriesFnEx` is defined inside the `builtin_initialize` that creates the extension and
thus cannot reference it. This state replicates `MapDeclarationExtension.find?`'s per-module
binary search without requiring the extension object.
-/
private structure ExportedAxiomsState where
  importedModuleEntries : Array (Array (Name × Array Name)) := #[]
  /-- Axiom dependencies of current-module declarations, filled eagerly by `recordAxioms`. -/
  localEntries : NameMap (Array Name) := {}

instance : Inhabited ExportedAxiomsState := ⟨{}⟩

/-- Look up pre-computed axioms for an imported or already-recorded local declaration. -/
private def ExportedAxiomsState.find? (s : ExportedAxiomsState) (env : Environment)
    (c : Name) : Option (Array Name) :=
  match env.getModuleIdxFor? c with
  | some modIdx =>
    if h : modIdx.toNat < s.importedModuleEntries.size then
      match s.importedModuleEntries[modIdx].binSearch (c, #[]) (fun a b => Name.quickLt a.1 b.1) with
      | some entry => some entry.2
      | none       => none
    else none
  | none => s.localEntries.find? c

/--
Environment extension that records axiom dependencies for all declarations in a module.
Entries for the current module are filled eagerly by `recordAxioms` as declarations pass the
kernel; the `sync` mode makes these writes accumulate along the `checked` environment chain so
that recording a declaration reuses the entries of all prior declarations. When the olean is
serialized, `exportEntriesFnEx` exports the entries of all exported declarations, computing any
entry missing due to e.g. realizations or error recovery. Downstream modules look up
pre-computed entries for imported declarations, so axiom collection never crosses module
boundaries.
-/
private builtin_initialize exportedAxiomsExt :
    PersistentEnvExtension (Name × Array Name) (Name × Array Name) ExportedAxiomsState ←
  registerPersistentEnvExtension {
    mkInitial     := pure {}
    addImportedFn := fun importedEntries => pure { importedModuleEntries := importedEntries }
    addEntryFn    := fun s _ => s
    exportEntriesFnEx := fun env s =>
      let exportedEnv := env.setExporting true
      let privateEnv := env.setExporting false
      -- Collect current-module declarations visible in the exported view.
      -- By pre-computing axiom data for every exported declaration, downstream modules can
      -- look up any imported declaration without walking its body, keeping collection
      -- module-local.
      let allNames := env.checked.get.constants.foldStage2
        (fun names name _ =>
          if (exportedEnv.find? name).isSome then names.push name
          else names) #[]
      -- Compute axioms within a shared state (for caching across declarations).
      -- Use `privateEnv` so that `collect` can see all constant bodies.
      let entries := CollectAxioms.runM privateEnv do
        allNames.mapM fun name =>
          return (name, ← CollectAxioms.collectAndGet s.find? name)
      -- Sort by name for binary search at import time.
      let entries := entries.qsort fun a b => Name.quickLt a.1 b.1
      .uniform entries
    asyncMode     := .sync
  }

/--
Computes and records the axiom dependencies of the given just-added declaration into
`exportedAxiomsExt`. Entries recorded for earlier declarations are reused, so each constant is
walked only once per module. Skipped in realization contexts, which would require extension
replay; declarations without an entry are walked on demand by `collectAxioms` instead.
-/
public def recordAxioms [Monad m] [MonadEnv m] (decl : Declaration) : m Unit := do
  let env ← getEnv
  if env.isRealizing then return
  let privateEnv := env.setExporting false
  let s := exportedAxiomsExt.getState env
  let (_, st) := decl.getTopLevelNames.mapM (CollectAxioms.collectAndGet s.find?)
    |>.run privateEnv |>.run {}
  -- `seen` contains exactly the walked constants; skip walked imported constants missing from
  -- the export table, which `find?` could never answer from `localEntries`.
  let newEntries := st.seen.foldl (init := #[]) fun acc c axs =>
    if (env.getModuleIdxFor? c).isNone then
      acc.push (c, axs)
    else
      acc
  unless newEntries.isEmpty do
    modifyEnv fun env => exportedAxiomsExt.modifyState env fun s =>
      { s with localEntries := newEntries.foldl (init := s.localEntries) fun m (c, axs) => m.insert c axs }

/-- Collect all axioms transitively used by a constant. -/
public def collectAxioms [Monad m] [MonadEnv m] (constName : Name) : m (Array Name) := do
  let env ← getEnv
  let privateEnv := env.setExporting false
  let s := exportedAxiomsExt.getState env
  return CollectAxioms.runM privateEnv do
    CollectAxioms.collectAndGet s.find? constName

end Lean
