/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lean.Data.Name
import Lean.Elab.Import
import Lake.BuildTarget
import Lake.BuildTop
import Lake.Resolve
import Lake.Package
import Lake.Compile

open System
open Lean hiding SearchPath

namespace Lake

-- # Build Targets

structure ModuleArtifact where
  oleanFile : FilePath
  cFile : FilePath
  deriving Inhabited

protected def ModuleArtifact.getMTime (self : ModuleArtifact) : IO MTime := do
  return max (← getMTime self.oleanFile) (← getMTime self.cFile)

instance : GetMTime ModuleArtifact := ⟨ModuleArtifact.getMTime⟩

abbrev ModuleTarget := LakeTarget ModuleArtifact

namespace ModuleTarget

def mk (olean c : FilePath) (hash : Hash) (mtime : IO.FS.SystemTime) (task : BuildTask) : ModuleTarget :=
  ActiveTarget.mk ⟨olean, c⟩ ⟨hash, mtime⟩ task

def pure (olean c : FilePath) (hash : Hash) (mtime : IO.FS.SystemTime) : ModuleTarget :=
  ActiveTarget.pure ⟨olean, c⟩ ⟨hash, mtime⟩

def oleanFile (self : ModuleTarget) := self.artifact.oleanFile
def oleanTarget (self : ModuleTarget) : ActiveFileTarget :=
  {self with artifact := self.oleanFile, trace := self.mtime}

def cFile (self : ModuleTarget) := self.artifact.cFile
def cTarget (self : ModuleTarget) : ActiveFileTarget :=
  {self with artifact := self.cFile, trace := self.mtime}

end ModuleTarget

abbrev PackageTarget :=  LakeTarget (Package × NameMap ModuleTarget)

namespace PackageTarget

def package (self : PackageTarget) :=
  self.artifact.1

def moduleTargetMap (self : PackageTarget) : NameMap ModuleTarget :=
  self.artifact.2

def moduleTargets (self : PackageTarget) : Array (Name × ModuleTarget) :=
  self.moduleTargetMap.fold (fun arr k v => arr.push (k, v)) #[]

end PackageTarget

-- # Trace Checking

/-- Check if `hash` matches that in the file give file. -/
def checkIfSameHash (hash : Hash) (file : FilePath) : IO Bool :=
  try
    let contents ← IO.FS.readFile file
    match contents.toNat? with
    | some h => Hash.mk h.toUInt64 == hash
    | none => false
  catch _ =>
    false

/-- Construct a no-op build task if the given condition holds, otherwise perform `build`. -/
def skipIf [Pure m] (cond : Bool) (build : m BuildTask) : m BuildTask := do
  if cond then pure BuildTask.nop else build

/--
  Construct a no-op target if the given artifact is up-to-date.
  Otherwise, construct a target with the given build task.
-/
def skipIfNewer [GetMTime a]
(artifact : a) (depMTime : MTime)
{m} [Monad m] [MonadLiftT IO m] [MonadExceptOf IO.Error m]
(build : m BuildTask) : m (ActiveBuildTarget MTime a) := do
  ActiveTarget.mk artifact depMTime <| ←
    skipIf (← checkIfNewer artifact depMTime) build

-- # Build Modules

/-
  Produces a recursive module target fetcher that
  builds the target module after waiting for `depsTarget` and
  its direct local imports (relative to `pkg`) to build.

  The module is built with the configuration from `pkg` and
  a `LEAN_PATH` that includes `oleanDirs`.
-/
def fetchAfterDirectLocalImports
(pkg : Package) (oleanDirs : List FilePath) (depsTarget : LakeTarget PUnit)
{m} [Monad m] [MonadLiftT IO m] [MonadExceptOf IO.Error m] : RecFetch Name ModuleTarget m :=
  let leanPath := SearchPath.toString <| pkg.oleanDir :: oleanDirs
  fun mod fetch => do
    let leanFile := pkg.modToSrc mod
    let contents ← IO.FS.readFile leanFile
    -- parse direct local imports
    let (imports, _, _) ← Elab.parseImports contents leanFile.toString
    let imports := imports.map (·.module) |>.filter (·.getRoot == pkg.moduleRoot)
    -- we fetch the import targets even if a rebuild is not required
    -- because other build processes (ex. `.o`) rely on the map being complete
    let importTargets ← imports.mapM fetch
    -- calculate trace
    let leanMTime ← getMTime leanFile
    let leanHash := Hash.compute contents
    let importHashes ← importTargets.map (·.hash)
    let importMTimes ← importTargets.map (·.mtime)
    let fullHash := Hash.mixList (leanHash :: depsTarget.hash :: importHashes)
    let maxMTime := MTime.listMax (leanMTime :: depsTarget.mtime :: importMTimes)
    let hashFile := pkg.modToHashFile mod
    let sameHash ← checkIfSameHash fullHash hashFile
    let mtime := ite sameHash 0 maxMTime
    -- construct target
    let cFile := pkg.modToC mod
    let oleanFile := pkg.modToOlean mod
    let importTasks := importTargets.map (·.task)
    ActiveTarget.mk ⟨oleanFile, cFile⟩ ⟨fullHash, mtime⟩ <| ←
      skipIf sameHash <| afterTaskList (depsTarget.task :: importTasks) do
        compileOleanAndC leanFile oleanFile cFile leanPath pkg.rootDir pkg.leanArgs
        IO.FS.writeFile hashFile fullHash.toString

/-
  Equivalent to `RBTopT (cmp := Name.quickCmp) Name ModuleTarget IO`.
  Phrased this way to use `NameMap`.
-/
abbrev ModuleTargetM :=
  EStateT (List Name) (NameMap ModuleTarget) IO

abbrev ModuleTargetFetch :=
  RecFetch Name ModuleTarget ModuleTargetM

def throwOnCycle (mx : IO (Except (List Name) α)) : IO α  :=
  mx >>= fun
  | Except.ok a => a
  | Except.error cycle =>
    let cycle := cycle.map (s!"  {·}")
    throw <| IO.userError s!"import cycle detected:\n{"\n".intercalate cycle}"

def Package.buildModuleTargetDAGFor
(mod : Name)  (oleanDirs : List FilePath) (depsTarget : LakeTarget PUnit)
(self : Package) : IO (ModuleTarget × NameMap ModuleTarget) := do
  let fetch := fetchAfterDirectLocalImports self oleanDirs depsTarget
  throwOnCycle <| buildRBTop fetch mod |>.run {}

def Package.buildModuleTargetDAG
(oleanDirs : List FilePath) (depsTarget : LakeTarget PUnit) (self : Package) :=
  self.buildModuleTargetDAGFor self.moduleRoot oleanDirs depsTarget

def Package.buildModuleTargets
(mods : List Name) (oleanDirs : List FilePath)
(depsTarget : LakeTarget PUnit) (self : Package)
: IO (List ModuleTarget) := do
  let fetch : ModuleTargetFetch :=
    fetchAfterDirectLocalImports self oleanDirs depsTarget
  throwOnCycle <| mods.mapM (buildRBTop fetch) |>.run' {}

-- # Configure/Build Packages

def Package.buildTargetWithDepTargetsFor
(mod : Name) (depTargets : List PackageTarget) (self : Package)
: IO PackageTarget := do
  let depsTarget ← LakeTarget.all <|
    (← self.buildMoreDepsTarget).withArtifact arbitrary :: depTargets
  let oLeanDirs := depTargets.map (·.package.oleanDir)
  let (target, targetMap) ← self.buildModuleTargetDAGFor mod oLeanDirs depsTarget
  return {target with artifact := ⟨self, targetMap⟩}

def Package.buildTargetWithDepTargets
(depTargets : List PackageTarget) (self : Package) : IO PackageTarget :=
  self.buildTargetWithDepTargetsFor self.moduleRoot depTargets

partial def Package.buildTarget (self : Package) : IO PackageTarget := do
  let deps ← solveDeps self
  -- build dependencies recursively
  -- TODO: share build of common dependencies
  let depTargets ← deps.mapM (·.buildTarget)
  self.buildTargetWithDepTargets depTargets

def Package.buildDepTargets (self : Package) : IO (List PackageTarget) := do
  let deps ← solveDeps self
  deps.mapM (·.buildTarget)

def Package.buildDeps (self : Package) : IO (List Package) := do
  let deps ← solveDeps self
  let targets ← deps.mapM (·.buildTarget)
  try targets.forM (·.materialize) catch e =>
    -- actual error has already been printed within the task
    throw <| IO.userError "Build failed."
  return deps

def configure (pkg : Package) : IO Unit :=
  discard pkg.buildDeps

def Package.build (self : Package) : IO PUnit := do
  let target ← self.buildTarget
  try target.materialize catch _ =>
    -- actual error has already been printed within the task
    throw <| IO.userError "Build failed."

def build (pkg : Package) : IO PUnit :=
  pkg.build

-- # Print Paths

def Package.buildModuleTargetsWithDeps
(deps : List Package) (mods : List Name)  (self : Package)
: IO (List ModuleTarget) := do
  let oleanDirs := deps.map (·.oleanDir)
  let depsTarget ← LakeTarget.all <|
    (← self.buildMoreDepsTarget).withArtifact arbitrary :: (← deps.mapM (·.buildTarget))
  self.buildModuleTargets mods oleanDirs depsTarget

def Package.buildModulesWithDeps
(deps : List Package) (mods : List Name)  (self : Package)
: IO PUnit := do
  let targets ← self.buildModuleTargetsWithDeps deps mods
  try targets.forM (·.materialize) catch e =>
    -- actual error has already been printed within target
    throw <| IO.userError "Build failed."

def printPaths (pkg : Package) (imports : List String := []) : IO Unit := do
  let deps ← solveDeps pkg
  unless imports.isEmpty do
    let imports := imports.map (·.toName)
    let localImports := imports.filter (·.getRoot == pkg.moduleRoot)
    pkg.buildModulesWithDeps deps localImports
  IO.println <| SearchPath.toString <| pkg.oleanDir :: deps.map (·.oleanDir)
  IO.println <| SearchPath.toString <| pkg.srcDir :: deps.map (·.srcDir)
