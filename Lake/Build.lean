/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lean.Data.Name
import Lean.Elab.Import
import Lake.BuildTarget
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

abbrev ModuleTarget := LeanTarget ModuleArtifact

namespace ModuleTarget

def mk (olean c : FilePath) (hash : Hash) (mtime : IO.FS.SystemTime) (task : BuildTask) : ModuleTarget :=
  BuildTarget.mk ⟨olean, c⟩ ⟨hash, mtime⟩ task

def pure (olean c : FilePath) (hash : Hash) (mtime : IO.FS.SystemTime) : ModuleTarget :=
  BuildTarget.pure ⟨olean, c⟩ ⟨hash, mtime⟩

def oleanFile (self : ModuleTarget) := self.artifact.oleanFile
def oleanTarget (self : ModuleTarget) : FileTarget :=
  {self with artifact := self.oleanFile, trace := self.mtime}

def cFile (self : ModuleTarget) := self.artifact.cFile
def cTarget (self : ModuleTarget) : FileTarget :=
  {self with artifact := self.cFile, trace := self.mtime}

end ModuleTarget

abbrev PackageTarget :=  LeanTarget (Package × NameMap ModuleTarget)

namespace PackageTarget

def package (self : PackageTarget) := self.artifact.1
def moduleTargets (self : PackageTarget) : NameMap ModuleTarget :=
  self.artifact.2

end PackageTarget

-- # Trace Checking

/-- Check if `hash` matches that in the file give file. -/
def checkIfSameHash (hash : Hash) (file : FilePath) : IO Bool :=
  try
    let contents ← IO.FS.readFile file
    match contents.toNat? with
    | some h => Hash.ofNat h == hash
    | none => false
  catch _ =>
    false

/-- Check if the artifact's `MTIme` is at least `depMTime`. -/
def checkIfNewer [GetMTime a] (artifact : a) (depMTime : MTime) : IO Bool := do
  try (← getMTime artifact) >= depMTime catch _ => false

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
(build : m BuildTask) : m (MTimeBuildTarget a) := do
  MTimeBuildTarget.mk artifact depMTime <| ←
    skipIf (← checkIfNewer artifact depMTime) build

-- # Build Components

def buildO (oFile : FilePath)
(cTarget : BuildTarget t FilePath) (leancArgs : Array String := #[]) : IO BuildTask :=
  afterTarget cTarget <| compileO oFile cTarget.artifact leancArgs

def fetchOFileTarget (oFile : FilePath)
(cTarget : FileTarget) (leancArgs : Array String := #[]) : IO FileTarget :=
  skipIfNewer oFile cTarget.mtime <| buildO oFile cTarget leancArgs

-- # Topological Builder

open Std

/-- A recursive object fetcher. -/
def RecFetch.{u,v,w} (k : Type u) (o : Type v) (m : Type v → Type w) :=
  k → (k → m o) → m o

/-- A exception plus state monad transformer (i.e., `StateT` + `ExceptT`). -/
abbrev EStateT (ε σ m) :=
  StateT σ <| ExceptT ε m

def EStateT.run (state : σ) (self : EStateT ε σ m α) : m (Except ε (α × σ)) :=
  StateT.run self state |>.run

def EStateT.run' [Monad m] (state : σ) (self : EStateT ε σ m α) : m (Except ε α) :=
  StateT.run' self state |>.run

/--
  Monad transformer for an RBMap-based topological walk.
  If a cycle is detected, the list keys traversed is thrown.
-/
abbrev RBTopT.{u,v} (k : Type u) (o : Type u) (cmp) (m : Type u → Type v) :=
  EStateT (List k) (RBMap k o cmp) m

/-- Auxiliary function for `buildRBTop`. -/
partial def buildRBTopCore
{k o} {cmp} {m : Type u → Type u} [BEq k] [Inhabited o] [Monad m]
(parents : List k) (fetch : RecFetch k o (RBTopT k o cmp m))
(key : k) : RBTopT k o cmp m o := do
  -- detect cyclic builds
  if parents.contains key then
    throw <| key :: (parents.partition (· != key)).1 ++ [key]
  -- return previous output if already built
  if let some output := (← get).find? key then
    return output
  -- build the key recursively
  let output ← fetch key (buildRBTopCore (key :: parents) fetch)
  -- save the output (to prevent repeated builds of the same key)
  modify (·.insert key output)
  return output

/--
  Recursively constructs an `RBMao` of key-object pairs by
  fetching objects topologically (i.e., via a deep-first search with
  memoization). Called a suspending scheduler in "Build systems à la carte".
-/
def buildRBTop {k o} {cmp} {m} [BEq k] [Inhabited o] [Monad m]
(fetch :  RecFetch k o (RBTopT k o cmp m)) (key : k) : RBTopT k o cmp m o :=
  buildRBTopCore [] fetch key

-- # Build Modules

/-
  Produces a recursive module target fetcher that
  builds the target module after waiting for `depsTarget` and
  its direct local imports (relative to `pkg`) to build.

  The module is built with the configuration from `pkg` and
  a `LEAN_PATH` that includes `oleanDirs`.
-/
def fetchAfterDirectLocalImports
(pkg : Package) (oleanDirs : List FilePath) (depsTarget : LeanTarget PUnit)
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
    let leanHash := hash contents
    let leanMTime ← getMTime leanFile
    let importHashes ← importTargets.map (·.hash)
    let importMTimes ← importTargets.map (·.mtime)
    let fullHash := Hash.foldList leanHash (depsTarget.hash :: importHashes)
    let maxMTime := MTime.listMax (leanMTime :: depsTarget.mtime :: importMTimes)
    let hashFile := pkg.modToHashFile mod
    let sameHash ← checkIfSameHash fullHash hashFile
    let mtime := ite sameHash 0 maxMTime
    -- construct target
    let cFile := pkg.modToC mod
    let oleanFile := pkg.modToOlean mod
    let importTasks := importTargets.map (·.buildTask)
    BuildTarget.mk ⟨oleanFile, cFile⟩ ⟨fullHash, mtime⟩ <| ←
      skipIf sameHash <| afterTaskList (depsTarget.buildTask :: importTasks) do
        compileOleanAndC leanFile oleanFile cFile leanPath pkg.dir pkg.leanArgs
        IO.FS.writeFile hashFile (toString fullHash)

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

def Package.buildModuleTargetDAG
(oleanDirs : List FilePath) (depsTarget : LeanTarget PUnit)
(self : Package) : IO (ModuleTarget × NameMap ModuleTarget) := do
  let fetch := fetchAfterDirectLocalImports self oleanDirs depsTarget
  throwOnCycle <| buildRBTop fetch self.moduleRoot |>.run {}

def Package.buildModuleTargets
(mods : List Name) (oleanDirs : List FilePath)
(depsTarget : LeanTarget PUnit) (self : Package)
: IO (List ModuleTarget) := do
  let fetch : ModuleTargetFetch :=
    fetchAfterDirectLocalImports self oleanDirs depsTarget
  throwOnCycle <| mods.mapM (buildRBTop fetch) |>.run' {}

-- # Configure/Build Packages

def Package.buildTargetWithDepTargets
(depTargets : List PackageTarget) (self : Package)
: IO PackageTarget := do
  let depsTarget ← LeanTarget.all <|
    self.moreDepsTarget.withArtifact arbitrary :: depTargets
  let oLeanDirs := depTargets.map (·.package.oleanDir)
  let (target, targetMap) ← self.buildModuleTargetDAG oLeanDirs depsTarget
  return {target with artifact := ⟨self, targetMap⟩}

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
  let depsTarget ← LeanTarget.all <|
    self.moreDepsTarget.withArtifact arbitrary :: (← deps.mapM (·.buildTarget))
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

-- # Build Package Lib

def PackageTarget.fetchOFileTargets
(self : PackageTarget) : IO (List FileTarget) := do
  self.moduleTargets.toList.mapM fun (mod, target) => do
    let oFile := self.package.modToO mod
    fetchOFileTarget (oFile) target.cTarget self.package.leancArgs

def PackageTarget.buildStaticLib
(self : PackageTarget) : IO BuildTask := do
  let oFileTargets ← self.fetchOFileTargets
  let oFiles := oFileTargets.map (·.artifact) |>.toArray
  oFileTargets >> compileStaticLib self.package.staticLibFile oFiles

def PackageTarget.fetchStaticLibTarget (self : PackageTarget) : IO FileTarget := do
  skipIfNewer self.package.staticLibFile self.mtime self.buildStaticLib

def Package.fetchStaticLibTarget (self : Package) : IO FileTarget := do
  (← self.buildTarget).fetchStaticLibTarget

def Package.fetchStaticLib (self : Package) : IO FilePath := do
  let target ← self.fetchStaticLibTarget
  try target.materialize catch _ =>
    -- actual error has already been printed within the task
    throw <| IO.userError "Build failed."
  return target.artifact

def buildLib (pkg : Package) : IO PUnit :=
  discard pkg.fetchStaticLib

-- # Build Package Bin

def PackageTarget.buildBin
(depTargets : List PackageTarget) (self : PackageTarget)
: IO BuildTask := do
  let oFileTargets ← self.fetchOFileTargets
  let libTargets ← depTargets.mapM (·.fetchStaticLibTarget)
  let linkTargets := oFileTargets ++ libTargets
  let linkFiles := linkTargets.map (·.artifact) |>.toArray
  linkTargets >> compileBin self.package.binFile linkFiles self.package.linkArgs

def PackageTarget.fetchBinTarget
(depTargets : List PackageTarget) (self : PackageTarget) : IO FileTarget :=
  skipIfNewer self.package.binFile self.mtime <| self.buildBin depTargets

def Package.fetchBinTarget (self : Package) : IO FileTarget := do
  let depTargets ← self.buildDepTargets
  let pkgTarget ← self.buildTargetWithDepTargets depTargets
  pkgTarget.fetchBinTarget depTargets

def Package.fetchBin (self : Package) : IO FilePath := do
  let target ← self.fetchBinTarget
  try target.materialize catch _ =>
    -- actual error has already been printed within the task
    throw <| IO.userError "Build failed."
  return target.artifact

def buildBin (pkg : Package) : IO PUnit :=
  discard pkg.fetchBin
