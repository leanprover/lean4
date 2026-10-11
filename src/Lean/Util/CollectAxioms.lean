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
  /-- Cache mapping constants to their (sorted) axiom dependencies. -/
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
for imported declarations. Results are cached in `State.seen`.

When processing a constant not found in `extFind?` or the cache, the function temporarily
clears the axiom accumulator, recurses into the constant's dependencies, caches the result
in `seen`, and merges the collected axioms back.

An inductive block is processed as a unit: all mutually declared types and their constructors
share the union of their axiom dependencies, even if some siblings do not refer to each other.
-/
private partial def collect
    (extFind? : Environment → Name → Option (Array Name))
    (c : Name) : M Unit := do
  let env ← read
  -- Check extension for pre-computed axioms (imported declarations)
  if let some axs := extFind? env c then
    modify fun s => { s with axioms := insertArray s.axioms axs, seen := s.seen.insert c axs }
    return
  -- Check local cache
  let s ← get
  if let some axs := s.seen.find? c then
    modify fun s => { s with axioms := insertArray s.axioms axs }
    return
  -- Recurse: temporarily clear axioms to isolate this constant's contribution.
  let savedAxioms := s.axioms
  -- The placeholder prevents infinite recursion, but does not ensure complete cached results
  -- for cycles outside the inductive blocks handled below (e.g., mutual unsafe definitions).
  modify fun s => { s with axioms := {}, seen := s.seen.insert c #[] }
  let collectExpr (e : Expr) : M Unit := e.getUsedConstants.forM (collect extFind?)
  let mut names := #[c]
  -- Take constants from the kernel env, which may differ from the elab env for (async) errors.
  match env.checked.get.find? c with
  | some (.axiomInfo v)  =>
      modify fun s => { s with axioms := s.axioms.insert c }
      collectExpr v.type
  | some (.defnInfo v)   => collectExpr v.type *> collectExpr v.value
  | some (.thmInfo v)    => collectExpr v.type *> collectExpr v.value
  | some (.opaqueInfo v) => collectExpr v.type *> collectExpr v.value
  | some (.quotInfo _)   => pure ()
  | some (.ctorInfo v)   => collect extFind? v.induct
  | some (.recInfo v)    => collectExpr v.type
  | some (.inductInfo v) =>
      let mut block := #[]
      for indName in v.all do
        if let some (.inductInfo ind) := env.checked.get.find? indName then
          block := block.push ind.toConstantVal
          for ctorName in ind.ctors do
            if let some (.ctorInfo ctor) := env.checked.get.find? ctorName then
              block := block.push ctor.toConstantVal
      names := block.map (·.name)
      -- Mark the whole block before walking any types, so internal edges cannot cache
      -- incomplete results for individual members.
      modify fun s => { s with seen := names.foldl (fun seen name => seen.insert name #[]) s.seen }
      for member in block do
        collectExpr member.type
  | none => pure ()
  -- Cache result (sorted for canonical order) and merge back into saved axioms
  let collected := (← get).axioms
  let result := collected.toArray.qsort Name.lt
  modify fun s => { s with
    seen   := names.foldl (fun seen name => seen.insert name result) s.seen
    axioms := insertArray savedAxioms result
  }

/-- Collect axioms for `c` and return its sorted axiom list from the cache. -/
private def collectAndGet
    (extFind? : Environment → Name → Option (Array Name))
    (c : Name) : M (Array Name) := do
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

instance : Inhabited ExportedAxiomsState := ⟨{}⟩

/-- Look up pre-computed axioms for an imported declaration. -/
private def ExportedAxiomsState.find? (s : ExportedAxiomsState) (env : Environment)
    (c : Name) : Option (Array Name) :=
  match env.getModuleIdxFor? c with
  | some modIdx =>
    if h : modIdx.toNat < s.importedModuleEntries.size then
      match s.importedModuleEntries[modIdx].binSearch (c, #[]) (fun a b => Name.quickLt a.1 b.1) with
      | some entry => some entry.2
      | none       => none
    else none
  | none => none

/--
Environment extension that records axiom dependencies for all declarations in a module.
Entries are computed once by `beforeExportFn` when the olean is serialized, not during
elaboration. During elaboration, `collectAxioms` walks bodies directly. Downstream modules
look up pre-computed entries for imported declarations, so axiom collection never crosses
module boundaries.
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
          if (exportedEnv.find? (skipRealize := true) name).isSome then names.push name
          else names) #[]
      -- Compute axioms within a shared state (for caching across declarations).
      -- Use `privateEnv` so that `collect` can see all constant bodies.
      let entries := CollectAxioms.runM privateEnv do
        allNames.mapM fun name =>
          return (name, ← CollectAxioms.collectAndGet s.find? name)
      -- Sort by name for binary search at import time.
      let entries := entries.qsort fun a b => Name.quickLt a.1 b.1
      .uniform entries
    asyncMode     := .mainOnly
  }

/-- Collect all axioms transitively used by a constant. -/
public def collectAxioms [Monad m] [MonadEnv m] (constName : Name) : m (Array Name) := do
  let env ← getEnv
  let privateEnv := env.setExporting false
  let s := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  return CollectAxioms.runM privateEnv do
    CollectAxioms.collectAndGet s.find? constName

end Lean
