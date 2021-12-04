/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Mac Malone
-/
import Lean.Data.Name
import Lean.Elab.Import
import Lake.Build.Target
import Lake.Build.Actions
import Lake.Build.Recursive
import Lake.Build.TargetTypes
import Lake.Config.Package

open System
open Lean hiding SearchPath

namespace Lake

-- # Targets

structure OleanAndC where
  oleanFile : FilePath
  cFile : FilePath
  deriving Inhabited, Repr

namespace OleanAndC

protected def getMTime (self : OleanAndC) : IO MTime := do
  return mixTrace (← getMTime self.oleanFile) (← getMTime self.cFile)

instance : GetMTime OleanAndC := ⟨OleanAndC.getMTime⟩

protected def computeHash (self : OleanAndC) : IO Hash := do
  return mixTrace (← computeHash self.oleanFile) (← computeHash self.cFile)

instance : ComputeHash OleanAndC := ⟨OleanAndC.computeHash⟩

protected def checkExists (self : OleanAndC) : BaseIO Bool := do
  return (← checkExists self.oleanFile) && (← checkExists self.cFile)

instance : CheckExists OleanAndC := ⟨OleanAndC.checkExists⟩

end OleanAndC

abbrev OleanAndCTarget := BuildTarget OleanAndC

namespace OleanAndCTarget

abbrev oleanFile (self : OleanAndCTarget) := self.info.oleanFile
def oleanTarget (self : OleanAndCTarget) : FileTarget :=
  Target.mk self.oleanFile do self.mapAsync fun i _ => computeTrace i.oleanFile

abbrev cFile (self : OleanAndCTarget) := self.info.cFile
def cTarget (self : OleanAndCTarget) : FileTarget :=
  Target.mk self.cFile do self.mapAsync fun i _ => computeTrace i.cFile

end OleanAndCTarget

structure ActiveOleanAndCTargets where
  oleanTarget : ActiveFileTarget
  cTarget : ActiveFileTarget
  deriving Inhabited

namespace ActiveOleanAndCTargets
abbrev oleanFile (self : ActiveOleanAndCTargets) := self.oleanTarget.info
abbrev cFile (self : ActiveOleanAndCTargets) := self.cTarget.info
end ActiveOleanAndCTargets

/--
An active module `.olean` and `.c` target consists of a single task that
builds both with two dependent targets that compute their individual traces.
-/
abbrev ActiveOleanAndCTarget := ActiveBuildTarget ActiveOleanAndCTargets

namespace ActiveOleanAndCTarget

abbrev oleanFile (self : ActiveOleanAndCTarget) := self.info.oleanFile
abbrev oleanTarget (self : ActiveOleanAndCTarget) := self.info.oleanTarget

abbrev cFile (self : ActiveOleanAndCTarget) := self.info.cFile
abbrev cTarget (self : ActiveOleanAndCTarget) := self.info.cTarget

end ActiveOleanAndCTarget

def OleanAndCTarget.run' (self : OleanAndCTarget) : BuildM ActiveOleanAndCTarget := do
  let t ← self.run
  let oleanTask ← t.mapAsync fun info depTrace => do
    return mixTrace (← computeTrace info.oleanFile) depTrace
  let cTask ← t.mapAsync fun info _ => do
    return mixTrace (← computeTrace info.cFile) (← getLeanTrace)
  return t.withInfo {
    oleanTarget := ActiveTarget.mk self.oleanFile oleanTask
    cTarget := ActiveTarget.mk self.cFile cTask
  }

-- # Module Builders

def moduleTarget [CheckExists i] [GetMTime i] [ComputeHash i] (info : i)
(leanFile traceFile : FilePath) (contents : String) (depTarget : BuildTarget x)
(build : BuildM PUnit) : BuildTarget i :=
  Target.mk info <| depTarget.mapOpaqueAsync fun depTrace => do
    let srcTrace : BuildTrace := ⟨Hash.ofString contents, ← getMTime leanFile⟩
    let fullTrace := (← getLeanTrace).mix <| srcTrace.mix depTrace
    let upToDate ← fullTrace.checkAgainstFile info traceFile
    unless upToDate do
      build
    fullTrace.writeToFile traceFile
    depTrace

def moduleOleanAndCTarget
(leanFile cFile oleanFile traceFile : FilePath)
(contents : String)  (depTarget : BuildTarget x)
(rootDir : FilePath := ".") (leanArgs : Array String := #[]) : OleanAndCTarget :=
  moduleTarget (OleanAndC.mk oleanFile cFile) leanFile traceFile contents depTarget do
    compileOleanAndC leanFile oleanFile cFile  (← getOleanDirs) rootDir leanArgs (← getLean)

def moduleOleanTarget
(leanFile oleanFile traceFile : FilePath)
(contents : String) (depTarget : BuildTarget x)
(rootDir : FilePath := ".") (leanArgs : Array String := #[]) : FileTarget :=
  let target := moduleTarget oleanFile leanFile traceFile contents depTarget do
    compileOlean leanFile oleanFile (← getOleanDirs) rootDir leanArgs (← getLean)
  target.withTask do target.mapAsync fun oleanFile depTrace => do
    return mixTrace (← computeTrace oleanFile) depTrace

protected def Package.moduleOleanAndCTargetOnly (self : Package)
(mod : Name) (leanFile : FilePath) (contents : String) (depTarget : BuildTarget x) :=
  let cFile := self.modToC mod
  let oleanFile := self.modToOlean mod
  let traceFile := self.modToTraceFile mod
  moduleOleanAndCTarget leanFile cFile oleanFile traceFile contents
    depTarget self.rootDir self.moreLeanArgs

protected def Package.moduleOleanTargetOnly (self : Package)
(mod : Name) (leanFile : FilePath) (contents : String) (depTarget : BuildTarget x) :=
  let oleanFile := self.modToOlean mod
  let traceFile := self.modToTraceFile mod
  moduleOleanTarget leanFile oleanFile traceFile contents depTarget
    self.rootDir self.moreLeanArgs

-- # Recursive Building

/-
  Produces a recursive module target builder that
  builds the target module after recursively building its local imports
  (relative to `pkg`).
-/
def recBuildModuleWithLocalImports (pkg : Package)
[Monad m] [MonadLiftT BuildM m] (build : Name → FilePath → String → List α → BuildM α)
: RecBuild Name α m := fun mod buildImp => do
  have : MonadLift BuildM m := ⟨liftM⟩
  let leanFile := pkg.modToSrc mod
  let contents ← IO.FS.readFile leanFile
  -- parse direct local imports
  let (imports, _, _) ← Elab.parseImports contents leanFile.toString
  let imports := imports.map (·.module) |>.filter pkg.isLocalModule
  -- we construct the import targets even if a rebuild is not required
  -- because other build processes (ex. `.o`) rely on the map being complete
  let importTargets ← imports.mapM buildImp
  build mod leanFile contents importTargets

def Package.recBuildModuleOleanAndCTargetWithLocalImports [Monad m] [MonadLiftT BuildM m]
(self : Package) (depTarget : ActiveBuildTarget x)
: RecBuild Name ActiveOleanAndCTarget m :=
  recBuildModuleWithLocalImports self fun mod leanFile contents importTargets => do
    let importTarget ← ActiveTarget.collectOpaqueList <| importTargets.map (·.oleanTarget)
    let allDepsTarget := Target.active <| ← depTarget.mixOpaqueAsync importTarget
    self.moduleOleanAndCTargetOnly mod leanFile contents allDepsTarget |>.run'

def Package.recBuildModuleOleanTargetWithLocalImports [Monad m] [MonadLiftT BuildM m]
(self : Package) (depTarget : ActiveBuildTarget x)
: RecBuild Name ActiveFileTarget m :=
  recBuildModuleWithLocalImports self fun mod leanFile contents importTargets => do
    let importTarget ← ActiveTarget.collectOpaqueList importTargets
    let allDepsTarget := Target.active <| ← depTarget.mixOpaqueAsync importTarget
    self.moduleOleanTargetOnly mod leanFile contents allDepsTarget |>.run

-- ## Definitions

abbrev ModuleBuildM (α) :=
  -- equivalent to `RBTopT (cmp := Name.quickCmp) Name α BuildM`.
  -- phrased this way to use `NameMap`
  EStateT (List Name) (NameMap α) BuildM

abbrev RecModuleBuild (o) :=
  RecBuild Name o (ModuleBuildM o)

abbrev RecModuleTargetBuild (i) :=
  RecModuleBuild (ActiveBuildTarget i)

-- ## Builders

def buildModule (mod : Name)
[Inhabited o] (build : RecModuleBuild o) : BuildM o := do
  failOnBuildCycle <| ← RBTopT.run' do
    buildRBTop (cmp := Name.quickCmp) build id mod

def buildModules (mods : Array Name)
[Inhabited o] (build : RecModuleBuild o) : BuildM (Array o) := do
  failOnBuildCycle <| ← RBTopT.run' <| mods.mapM do
    buildRBTop (cmp := Name.quickCmp) build id
