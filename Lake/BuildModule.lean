/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lean.Data.Name
import Lean.Elab.Import
import Lake.Target
import Lake.BuildTarget
import Lake.BuildTop
import Lake.Compile
import Lake.Package

open System
open Lean hiding SearchPath

namespace Lake

-- # Build Target

structure ModuleArtifact where
  oleanFile : FilePath
  cFile : FilePath
  deriving Inhabited

protected def ModuleArtifact.getMTime (self : ModuleArtifact) : IO MTime := do
  return max (← getMTime self.oleanFile) (← getMTime self.cFile)

instance : GetMTime ModuleArtifact := ⟨ModuleArtifact.getMTime⟩

abbrev ModuleTarget := ActiveBuildTarget ModuleArtifact

namespace ModuleTarget

def oleanFile (self : ModuleTarget) := self.artifact.oleanFile
def oleanTarget (self : ModuleTarget) : ActiveFileTarget :=
  {self with artifact := self.oleanFile}

def cFile (self : ModuleTarget) := self.artifact.cFile
def cTarget (self : ModuleTarget) : ActiveFileTarget :=
  {self with artifact := self.cFile}

end ModuleTarget

-- # Trace Checking

/-- Check if `hash` matches that in the given file. -/
def checkIfSameHash (hash : Hash) (file : FilePath) : IO Bool :=
  try
    let contents ← IO.FS.readFile file
    match contents.toNat? with
    | some h => Hash.mk h.toUInt64 == hash
    | none => false
  catch _ =>
    false

/-- Construct a no-op build task if the given condition holds, otherwise perform `build`. -/
def skipIf [Pure m] [Pure n] (cond : Bool) (build : m (n PUnit)) : m (n PUnit) := do
  if cond then pure (pure ()) else build

-- # Build Modules

/-
  Produces a recursive module target fetcher that
  builds the target module after waiting for `depTargets` to materialize
  and recursively fetching its local imports (relative to `pkg`).

  The module is built with the configuration from `pkg` and
  a `LEAN_PATH` that includes `oleanDirs`.
-/
def fetchModuleWithLocalImports
(pkg : Package) (oleanDirs : List FilePath) (depTarget : ActiveOpaqueTarget)
{m} [Monad m] [MonadLiftT BuildM m] [MonadExceptOf IO.Error m] : RecFetch Name ModuleTarget m :=
  have : MonadLift BuildM m := ⟨liftM⟩
  let leanPath := SearchPath.toString <| pkg.oleanDir :: oleanDirs
  fun mod fetch => do
    let leanFile := pkg.modToSrc mod
    let contents ← liftM (m := BuildM) <| IO.FS.readFile leanFile
    -- parse direct local imports
    let (imports, _, _) ← Elab.parseImports contents leanFile.toString
    let imports := imports.map (·.module) |>.filter (·.getRoot == pkg.moduleRoot)
    -- we fetch the import targets even if a rebuild is not required
    -- because other build processes (ex. `.o`) rely on the map being complete
    let importTargets ← imports.mapM fetch
    -- calculate trace
    let leanMTime ← getMTime leanFile
    let leanHash := Hash.compute contents
    let depTrace := mixTrace depTarget.trace
      (mixTraceList  <| importTargets.map  (·.trace))
    let maxMTime := max leanMTime depTrace.mtime
    let fullHash := Hash.mix leanHash depTrace.hash
    let hashFile := pkg.modToHashFile mod
    let sameHash ← checkIfSameHash fullHash hashFile
    let mtime := ite sameHash 0 maxMTime
    -- construct target
    let cFile := pkg.modToC mod
    let oleanFile := pkg.modToOlean mod
    let depTasks := depTarget.task :: importTargets.map (·.task)
    ActiveTarget.mk ⟨oleanFile, cFile⟩ ⟨fullHash, mtime⟩ <| ←
      skipIf sameHash <| afterTaskList (m := BuildM) depTasks do
        compileOleanAndC leanFile oleanFile cFile leanPath pkg.rootDir pkg.leanArgs
        IO.FS.writeFile hashFile fullHash.toString

abbrev ModuleTargetMap := NameMap ModuleTarget

/-
  Equivalent to `RBTopT (cmp := Name.quickCmp) Name ModuleTarget BuildM`.
  Phrased this way to use `ModuleTargetMap`.
-/
abbrev ModuleTargetM :=
  EStateT (List Name) ModuleTargetMap BuildM

abbrev ModuleTargetFetch :=
  RecFetch Name ModuleTarget ModuleTargetM

def failOnCycle : Except (List Name) α → BuildM α
| Except.ok a => a
| Except.error cycle => do
  let cycle := cycle.map (s!"  {·}")
  let msg := s!"import cycle detected:\n{"\n".intercalate cycle}"
  BuildM.logError msg
  throw <| IO.userError msg
