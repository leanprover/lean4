/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.MonadEnv

namespace Lean

public register_builtin_option trackAxioms : Bool := {
  defValue := true
  descr    := "record the axioms each declaration of the module depends on, for use by \
    `#print axioms`. When disabled, the module's `.olean` does not depend on the axioms used in \
    proofs, and `#print axioms` refers to `lake check` instead. Only takes effect when passed to \
    the module as a whole, e.g. via `leanOptions` in the Lake configuration."
}

/--
Root of the pseudo-axiom names that stand for the unknown axioms of declarations from a module
compiled with `trackAxioms := false`. A numeric root cannot occur in declaration names.
-/
private def untrackedRoot : Name := .num .anonymous 0

private def mkUntrackedMarker (mod : Name) : Name := untrackedRoot ++ mod

private def untrackedModule? (n : Name) : Option Name :=
  if untrackedRoot.isPrefixOf n && n != untrackedRoot then
    some (n.replacePrefix untrackedRoot .anonymous)
  else
    none

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
  /-- Value of `trackAxioms` for the current module. -/
  track : Bool := true

instance : Inhabited ExportedAxiomsState := ⟨{}⟩

/-- The sole entry exported by a module compiled with `trackAxioms := false`. -/
private def untrackedModuleEntry : Name × Array Name := (.anonymous, #[])

/--
Look up pre-computed axioms for an imported declaration. For a declaration from a module compiled
with `trackAxioms := false`, returns that module's untracked marker.
-/
private def ExportedAxiomsState.find? (s : ExportedAxiomsState) (env : Environment)
    (c : Name) : Option (Array Name) :=
  match env.getModuleIdxFor? c with
  | some modIdx =>
    if h : modIdx.toNat < s.importedModuleEntries.size then
      let entries := s.importedModuleEntries[modIdx]
      if entries[0]?.any (·.1.isAnonymous) then
        some #[mkUntrackedMarker env.allImportedModuleNames[modIdx]!]
      else
        match entries.binSearch (c, #[]) (fun a b => Name.quickLt a.1 b.1) with
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

A module compiled with `trackAxioms := false` exports only `untrackedModuleEntry`. Axiom sets of
declarations depending on it contain its untracked marker (see `untrackedRoot`), which downstream
entries inherit.
-/
private builtin_initialize exportedAxiomsExt :
    PersistentEnvExtension (Name × Array Name) (Name × Array Name) ExportedAxiomsState ←
  registerPersistentEnvExtension {
    mkInitial     := pure {}
    addImportedFn := fun importedEntries => return {
      importedModuleEntries := importedEntries
      track := trackAxioms.get (← read).opts
    }
    addEntryFn    := fun s _ => s
    exportEntriesFnEx := fun env s => if !s.track then .uniform #[untrackedModuleEntry] else
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
    asyncMode     := .mainOnly
  }

/-- Result of `collectAxiomsCore`. -/
public structure CollectedAxioms where
  /-- Axioms the constant is known to depend on, sorted. -/
  axioms : Array Name
  /--
  Modules compiled with `trackAxioms := false` that the constant depends on. If nonempty, `axioms`
  may be incomplete.
  -/
  untrackedModules : Array Name

/--
Collects the axioms transitively used by a constant, reporting dependencies on modules compiled
with `trackAxioms := false` instead of failing on them.
-/
public def collectAxiomsCore [Monad m] [MonadEnv m] (constName : Name) : m CollectedAxioms := do
  let env ← getEnv
  let privateEnv := env.setExporting false
  let s := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let all := CollectAxioms.runM privateEnv do
    CollectAxioms.collectAndGet s.find? constName
  return {
    axioms := all.filter (untrackedModule? · |>.isNone)
    untrackedModules := all.filterMap untrackedModule?
  }

/--
Collects all axioms transitively used by a constant. Throws an error referring to `lake check` if
the current module or a module the constant depends on is compiled with `trackAxioms := false`.
-/
public def collectAxioms [Monad m] [MonadEnv m] [MonadError m] (constName : Name) :
    m (Array Name) := do
  unless (exportedAxiomsExt.getState (asyncMode := .mainOnly) (← getEnv)).track do
    throwError "cannot collect the axioms of '{.ofConstName constName}': axiom tracking is \
      disabled in the current module (`trackAxioms := false`); use `lake check` to check the \
      axioms used by the project instead"
  let r ← collectAxiomsCore constName
  unless r.untrackedModules.isEmpty do
    let mods := ", ".intercalate (r.untrackedModules.toList.map (s!"`{·}`"))
    throwError "cannot collect the axioms of '{.ofConstName constName}': it depends on \
      declarations from {mods}, compiled with `trackAxioms := false`; use `lake check` to check \
      the axioms used by the project instead"
  return r.axioms

end Lean
