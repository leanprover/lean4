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

-- # Targets

abbrev OleanTarget := ActiveFileTarget

structure ModuleArtifact where
  oleanFile : FilePath
  cFile : FilePath
  deriving Inhabited

namespace ModuleArtifact

protected def getMTime (self : ModuleArtifact) : IO MTime := do
  return mixTrace (← getMTime self.oleanFile) (← getMTime self.cFile)

instance : GetMTime ModuleArtifact := ⟨ModuleArtifact.getMTime⟩

protected def computeHash (self : ModuleArtifact) : IO Hash := do
  return mixTrace (← computeHash self.oleanFile) (← computeHash self.cFile)

instance : ComputeHash ModuleArtifact := ⟨ModuleArtifact.computeHash⟩

end ModuleArtifact

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

def checkModuleTrace [GetMTime a] (artifact : a)
(leanFile hashFile : FilePath) (contents : String) (depTrace : LakeTrace)
: IO (Bool × LakeTrace) := do
  let leanMTime ← getMTime leanFile
  let leanHash := Hash.compute contents
  let maxMTime := max leanMTime depTrace.mtime
  let fullHash := Hash.mix leanHash depTrace.hash
  try
    discard <| getMTime artifact -- ensure the artifact actually exists
    let sameHash ← checkIfSameHash fullHash hashFile
    let mtime := ite sameHash 0 maxMTime
    (sameHash, ⟨fullHash, mtime⟩)
  catch _ =>
    (false, ⟨fullHash, maxMTime⟩)

-- # Module Builders

def fetchModuleTarget (pkg : Package) (moreOleanDirs : List FilePath)
(mod : Name) (leanFile : FilePath) (contents : String) (depTarget : ActiveOpaqueTarget)
: BuildM ModuleTarget := do
  let cFile := pkg.modToC mod
  let oleanFile := pkg.modToOlean mod
  let artifact := ModuleArtifact.mk oleanFile cFile
  let hashFile := pkg.modToHashFile mod
  let oleanDirs :=  pkg.oleanDir :: moreOleanDirs
  let (upToDate, trace) ← checkModuleTrace artifact leanFile hashFile contents depTarget.trace
  ActiveTarget.mk artifact trace <| ← skipIf upToDate <| depTarget.andThen do
    compileOleanAndC leanFile oleanFile cFile oleanDirs pkg.rootDir pkg.leanArgs
    IO.FS.writeFile hashFile trace.hash.toString

def fetchModuleOleanTarget (pkg : Package) (moreOleanDirs : List FilePath)
(mod : Name) (leanFile : FilePath) (contents : String) (depTarget : ActiveOpaqueTarget)
: BuildM OleanTarget := do
  let oleanFile := pkg.modToOlean mod
  let hashFile := pkg.modToHashFile mod
  let oleanDirs := pkg.oleanDir :: moreOleanDirs
  let (upToDate, trace) ← checkModuleTrace oleanFile leanFile hashFile contents depTarget.trace
  ActiveTarget.mk oleanFile trace <| ← skipIf upToDate <| depTarget.andThen do
    compileOlean leanFile oleanFile oleanDirs pkg.rootDir pkg.leanArgs
    IO.FS.writeFile hashFile trace.hash.toString

-- # Recursive Fetching

/-
  Produces a recursive module target fetcher that
  builds the target module after recursively fetching its local imports
  (relative to `pkg`).
-/
def recFetchModuleWithLocalImports (pkg : Package)
[Monad m] [MonadLiftT BuildM m] (build : Name → FilePath → String → List α → m α)
: RecFetch Name α m := fun mod fetch => do
  have : MonadLift BuildM m := ⟨liftM⟩
  let leanFile := pkg.modToSrc mod
  let contents ← IO.FS.readFile leanFile
  -- parse direct local imports
  let (imports, _, _) ← Elab.parseImports contents leanFile.toString
  let imports := imports.map (·.module) |>.filter (·.getRoot == pkg.moduleRoot)
  -- we fetch the import targets even if a rebuild is not required
  -- because other build processes (ex. `.o`) rely on the map being complete
  let importTargets ← imports.mapM fetch
  build mod leanFile contents importTargets

def recFetchModuleTargetWithLocalImports [Monad m] [MonadLiftT BuildM m]
(pkg : Package) (moreOleanDirs : List FilePath) (depTarget : ActiveOpaqueTarget)
: RecFetch Name ModuleTarget m :=
  recFetchModuleWithLocalImports pkg fun mod leanFile contents importTargets => do
    let importTarget ← ActiveOpaqueTarget.collectList importTargets
    let allDepTarget ← depTarget.andThenTargetAsync importTarget
    fetchModuleTarget pkg moreOleanDirs mod leanFile contents allDepTarget

def recFetchModuleOleanTargetWithLocalImports [Monad m] [MonadLiftT BuildM m]
(pkg : Package) (moreOleanDirs : List FilePath) (depTarget : ActiveOpaqueTarget)
: RecFetch Name OleanTarget m :=
  recFetchModuleWithLocalImports pkg fun mod leanFile contents importTargets => do
    let importTarget ← ActiveOpaqueTarget.collectList importTargets
    let allDepTarget ← depTarget.andThenTargetAsync importTarget
    fetchModuleOleanTarget pkg moreOleanDirs mod leanFile contents allDepTarget

-- ## Definitions

abbrev ModuleFetchM (α) :=
  -- equivalent to `RBTopT (cmp := Name.quickCmp) Name ModuleTarget BuildM`.
  -- phrased this way to use `NameMap`
  EStateT (List Name) (NameMap α) BuildM

abbrev ModuleFetch (α) :=
  RecFetch Name α (ModuleFetchM α)

abbrev OleanTargetFetch := ModuleFetch OleanTarget
abbrev ModuleTargetFetch := ModuleFetch ModuleTarget

abbrev OleanTargetMap := NameMap OleanTarget
abbrev ModuleTargetMap := NameMap ModuleTarget
