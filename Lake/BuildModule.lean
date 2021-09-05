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

structure ModuleTargetInfo where
  oleanFile : FilePath
  cFile : FilePath
  deriving Inhabited

namespace ModuleArtifact

protected def getMTime (self : ModuleTargetInfo) : IO MTime := do
  return mixTrace (← getMTime self.oleanFile) (← getMTime self.cFile)

instance : GetMTime ModuleTargetInfo := ⟨ModuleArtifact.getMTime⟩

protected def computeHash (self : ModuleTargetInfo) : IO Hash := do
  return mixTrace (← computeHash self.oleanFile) (← computeHash self.cFile)

instance : ComputeHash ModuleTargetInfo := ⟨ModuleArtifact.computeHash⟩

end ModuleArtifact

abbrev ActiveModuleTarget := ActiveBuildTarget ModuleTargetInfo

namespace ActiveModuleTarget

def oleanFile (self : ActiveModuleTarget) := self.info.oleanFile
def oleanTarget (self : ActiveModuleTarget) : ActiveFileTarget :=
  self.withInfo self.oleanFile

def cFile (self : ActiveModuleTarget) := self.info.cFile
def cTarget (self : ActiveModuleTarget) : ActiveFileTarget :=
  self.withInfo self.cFile

end ActiveModuleTarget

-- # Trace Checking

def checkModuleTrace [GetMTime i] (info : i)
(leanFile hashFile : FilePath) (contents : String) (depTrace : BuildTrace)
: IO (Bool × BuildTrace) := do
  let leanMTime ← getMTime leanFile
  let leanHash := Hash.compute contents
  let maxMTime := max leanMTime depTrace.mtime
  let fullHash := Hash.mix leanHash depTrace.hash
  try
    discard <| getMTime info -- check that both output files exist
    if let some h ← Hash.fromFile hashFile then
      if h == fullHash then return (true, BuildTrace.fromHash fullHash)
  catch _ =>
    pure ()
  return (false, BuildTrace.mk fullHash maxMTime)

-- # Module Builders

def mkModuleTarget [GetMTime i] [ComputeHash i] (info : i)
(leanFile hashFile : FilePath) (contents : String) (depTarget : ActiveOpaqueTarget)
(build : BuildM PUnit) : BuildM (ActiveBuildTarget i) := do
  ActiveTarget.mk info <| ← depTarget.mapOpaqueAsync fun depTrace => do
    let (upToDate, trace) ← checkModuleTrace info leanFile hashFile contents depTrace
    if upToDate then
      BuildTrace.fromHash <| (← computeHash info).mix depTrace.hash
    else
      build
      IO.FS.writeFile hashFile trace.hash.toString
       let newTrace : BuildTrace ← liftM <| computeTrace info
      newTrace.mix depTrace

def fetchModuleTarget (pkg : Package) (moreOleanDirs : List FilePath)
(mod : Name) (leanFile : FilePath) (contents : String) (depTarget : ActiveOpaqueTarget)
: BuildM ActiveModuleTarget := do
  let cFile := pkg.modToC mod
  let oleanFile := pkg.modToOlean mod
  let info := ModuleTargetInfo.mk oleanFile cFile
  let hashFile := pkg.modToHashFile mod
  let oleanDirs :=  pkg.oleanDir :: moreOleanDirs
  mkModuleTarget  info leanFile hashFile contents depTarget <|
    compileOleanAndC leanFile oleanFile cFile oleanDirs pkg.rootDir pkg.leanArgs

def fetchModuleOleanTarget (pkg : Package) (moreOleanDirs : List FilePath)
(mod : Name) (leanFile : FilePath) (contents : String) (depTarget : ActiveOpaqueTarget)
: BuildM OleanTarget := do
  let oleanFile := pkg.modToOlean mod
  let hashFile := pkg.modToHashFile mod
  let oleanDirs := pkg.oleanDir :: moreOleanDirs
  mkModuleTarget oleanFile leanFile hashFile contents depTarget <|
    compileOlean leanFile oleanFile oleanDirs pkg.rootDir pkg.leanArgs

-- # Recursive Fetching

/-
  Produces a recursive module target fetcher that
  builds the target module after recursively fetching its local imports
  (relative to `pkg`).
-/
def recFetchModuleWithLocalImports (pkg : Package)
[Monad m] [MonadLiftT BuildM m] (build : Name → FilePath → String → List α → BuildM α)
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
: RecFetch Name ActiveModuleTarget m :=
  recFetchModuleWithLocalImports pkg fun mod leanFile contents importTargets => do
    let allDepsTarget ← depTarget.mixOpaqueAsync <| ← ActiveTarget.collectOpaqueList importTargets
    fetchModuleTarget pkg moreOleanDirs mod leanFile contents allDepsTarget

def recFetchModuleOleanTargetWithLocalImports [Monad m] [MonadLiftT BuildM m]
(pkg : Package) (moreOleanDirs : List FilePath) (depTarget : ActiveOpaqueTarget)
: RecFetch Name OleanTarget m :=
  recFetchModuleWithLocalImports pkg fun mod leanFile contents importTargets => do
    let allDepsTarget ← depTarget.mixOpaqueAsync <| ← ActiveTarget.collectOpaqueList importTargets
    fetchModuleOleanTarget pkg moreOleanDirs mod leanFile contents allDepsTarget

-- ## Definitions

abbrev ModuleFetchM (α) :=
  -- equivalent to `RBTopT (cmp := Name.quickCmp) Name ActiveModuleTarget BuildM`.
  -- phrased this way to use `NameMap`
  EStateT (List Name) (NameMap α) BuildM

abbrev ModuleFetch (α) :=
  RecFetch Name α (ModuleFetchM α)

abbrev OleanTargetFetch := ModuleFetch OleanTarget
abbrev ModuleTargetFetch := ModuleFetch ActiveModuleTarget

abbrev OleanTargetMap := NameMap OleanTarget
abbrev ModuleTargetMap := NameMap ActiveModuleTarget
