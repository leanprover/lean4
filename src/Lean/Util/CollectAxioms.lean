/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.MonadEnv
import Lean.OriginalConstKind
public import Lean.CoreM
import Lean.Util.LakePath
import Lean.Util.Path
import Lean.Data.Json

namespace Lean

/-- Result of `collectAxiomsCore`. -/
public structure CollectedAxioms where
  /-- Axioms found in the loaded part of the constant's dependencies, sorted. -/
  axioms : Array Name := #[]
  /--
  Imported constants the constant depends on whose bodies are not loaded, sorted: under the module
  system, imported theorems and non-exposed definitions are represented as axioms. The axioms such
  constants depend on cannot be collected from the current environment.
  -/
  unresolved : Array Name := #[]
  deriving Inhabited

namespace CollectAxioms

structure Context where
  env : Environment
  /-- Do not inspect imported declarations other than axioms. -/
  localOnly : Bool := false

structure State where
  /-- Cache mapping constants to their dependencies. -/
  seen       : NameMap CollectedAxioms := {}
  /-- Axioms accumulated for the current constant being processed. -/
  axioms     : NameSet := {}
  /-- Constants without loaded body accumulated for the current constant being processed. -/
  unresolved : NameSet := {}

abbrev M := ReaderT Context $ StateM State

def runM (env : Environment) (x : M α) (localOnly := false) : α :=
  x.run { env, localOnly } |>.run' {}

def insertArray (s : NameSet) (axs : Array Name) : NameSet :=
  axs.foldl (init := s) fun acc ax => acc.insert ax

/--
Collect axioms reachable from constant `c`. Results are cached in `State.seen`.

When processing a constant not found in the cache, the function temporarily clears the
accumulators, recurses into the constant's dependencies, caches the result in `seen`, and merges
the collected names back.
-/
partial def collect (c : Name) : M Unit := do
  let { env, localOnly } ← read
  let s ← get
  if let some r := s.seen.find? c then
    modify fun s => { s with
      axioms     := insertArray s.axioms r.axioms
      unresolved := insertArray s.unresolved r.unresolved
    }
    return
  -- Recurse: temporarily clear the accumulators to isolate this constant's contribution.
  -- Insert sentinel to prevent infinite recursion (e.g., inductives ↔ constructors).
  let savedAxioms := s.axioms
  let savedUnresolved := s.unresolved
  modify fun s => { s with axioms := {}, unresolved := {}, seen := s.seen.insert c {} }
  let collectExpr (e : Expr) : M Unit := e.getUsedConstants.forM collect
  -- Take constants from the kernel env, which may differ from the elab env for (async) errors.
  let info? := env.checked.get.find? c
  let info? :=
    if localOnly && (env.getModuleIdxFor? c).isSome && !(info? matches some (.axiomInfo _)) then
      none
    else info?
  match info? with
  | some (.axiomInfo v)  =>
      -- An imported axiom of another original kind is a declaration whose body is not loaded.
      -- Declarations of the current module rejected by the kernel are such axioms as well, but
      -- there is nothing further to resolve for them.
      if (env.getModuleIdxFor? c).isSome && !(getOriginalConstKind? env c matches some .axiom) then
        modify fun s => { s with unresolved := s.unresolved.insert c }
      else
        modify fun s => { s with axioms := s.axioms.insert c }
      collectExpr v.type
  | some (.defnInfo v)   => collectExpr v.type *> collectExpr v.value
  | some (.thmInfo v)    => collectExpr v.type *> collectExpr v.value
  | some (.opaqueInfo v) => collectExpr v.type *> collectExpr v.value
  | some (.quotInfo _)   => pure ()
  | some (.ctorInfo v)   => collectExpr v.type
  | some (.recInfo v)    => collectExpr v.type
  | some (.inductInfo v) => collectExpr v.type *> v.ctors.forM collect
  | none                 => pure ()
  -- Cache result (sorted for canonical order) and merge back into the saved accumulators
  let s ← get
  let result : CollectedAxioms := {
    axioms     := s.axioms.toArray.qsort Name.lt
    unresolved := s.unresolved.toArray.qsort Name.lt
  }
  modify fun s => { s with
    seen       := s.seen.insert c result
    axioms     := insertArray savedAxioms result.axioms
    unresolved := insertArray savedUnresolved result.unresolved
  }

/-- Collect axioms for `c` and return its result from the cache. -/
def collectAndGet (c : Name) : M CollectedAxioms := do
  collect c
  let some r := (← get).seen.find? c | panic! s!"collectAndGet: '{c}' not in seen after collect"
  return r

end CollectAxioms

/--
Collects the axioms used by a constant as far as they can be determined from the current
environment, without consulting data of imported modules that is not loaded.

With `localOnly`, imported declarations other than axioms are not inspected at all, which avoids
walking the potentially large dependency closure in imported modules.
-/
public def collectAxiomsCore [Monad m] [MonadEnv m] (constName : Name) (localOnly := false) :
    m CollectedAxioms := do
  let env := (← getEnv).setExporting false
  return CollectAxioms.runM env (localOnly := localOnly) do
    CollectAxioms.collectAndGet constName

namespace CollectAxioms

/-- Request to `lake collect-axioms`. -/
public structure Request where
  /-- The direct imports of the requesting module. -/
  imports : Array Import
  searchPath : Array System.FilePath
  /-- The imported constants to collect the axioms of. -/
  consts : Array Name
  deriving ToJson, FromJson

/--
Implementation of `lake collect-axioms`: imports the modules of the request with all private data,
locating them via `importArts` and otherwise the search path, and returns the axioms of each
requested constant.
-/
public def handleRequest (req : Request) (importArts : NameMap ImportArtifacts) :
    IO (Array (Array Name)) := do
  searchPathRef.set req.searchPath.toList
  let env ← importModules req.imports {} (level := .private) (arts := importArts)
    (loadExts := false)
  let results := runM env do
    req.consts.mapM collectAndGet
  return results.map (·.axioms)

/-- Axioms of imported constants computed by `lake collect-axioms`, for the given imports. -/
builtin_initialize resolvedRef : IO.Ref (Array Import × NameMap (Array Name)) ←
  IO.mkRef (#[], {})

/--
Collects the axioms of imported constants whose bodies are not loaded by running
`lake collect-axioms` on the private data of the imported modules.
-/
def resolveImported (env : Environment) (fileName : String) (inServer : Bool)
    (consts : Array Name) : IO (Array Name) := do
  let imports := env.header.imports
  let (cachedImports, cached) ← resolvedRef.get
  -- `imports` should not change within a single worker process but let's just be safe in case of
  -- any other callers.
  let mut cached := if cachedImports == imports then cached else {}
  let missing := consts.filter (!cached.contains ·)
  unless missing.isEmpty do
    let req : Request := {
      imports
      searchPath := (← searchPathRef.get).toArray
      consts := missing
    }
    let out ← IO.Process.output (input? := (toJson req).compress ++ "\n") {
      cmd := (← determineLakePath).toString
      -- This query should neither build nor download anything.
      args := #["collect-axioms", fileName, "--no-build", "--no-cache"]
    }
    match out.exitCode with
    | 0 => pure ()
    | 3 => throw <| .userError <| "imports are out of date and must be rebuilt" ++
        if inServer then "; use the \"Restart File\" command in your editor." else ""
    | _ => throw <| .userError s!"`lake collect-axioms` failed:\n{out.stderr}\n\
        Use `lake check` to check the axioms used by the project instead."
    let results : Array (Array Name) ← IO.ofExcept <| Json.parse out.stdout >>= fromJson?
    unless results.size == missing.size do
      throw <| .userError "`lake collect-axioms` returned an unexpected number of results"
    for c in missing, axs in results do
      cached := cached.insert c axs
    resolvedRef.set (imports, cached)
  return consts.flatMap (cached.getD · #[])

end CollectAxioms

/--
Collects all axioms transitively used by a constant.

Under the module system, the proofs and non-exposed bodies of imported declarations are not
loaded. If the constant depends on such declarations, their axioms are collected by a separate
process that loads the private data of the imported modules; this requires that data to be
available and, in a Lake project, the imports to be up to date.
-/
public def collectAxioms [Monad m] [MonadEnv m] [MonadLog m] [MonadOptions m] [MonadLiftT IO m]
    (constName : Name) : m (Array Name) := do
  let { axioms, unresolved } ← collectAxiomsCore constName
  if unresolved.isEmpty then
    return axioms
  let env ← getEnv
  let fileName ← getFileName
  let inServer := Elab.inServer.get (← getOptions)
  let resolved ← (show IO _ from
    try
      CollectAxioms.resolveImported env fileName inServer unresolved
    catch e =>
      throw <| .userError s!"failed to collect the axioms of imported declarations: {e}")
  let all := resolved.foldl (init := axioms.foldl (·.insert ·) ({} : NameSet)) (·.insert ·)
  return all.toArray.qsort Name.lt

end Lean
