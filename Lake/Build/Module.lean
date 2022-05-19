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

-- # Info

structure Module where
  pkg : Package
  name : Name
  deriving Inhabited

namespace Module

@[inline] def srcFile (self : Module) : FilePath :=
  self.pkg.modToSrc self.name

@[inline] def oleanFile (self : Module) : FilePath :=
  self.pkg.modToOlean self.name

@[inline] def ileanFile (self : Module) : FilePath :=
  self.pkg.modToIlean self.name

@[inline] def cFile (self : Module) : FilePath :=
  self.pkg.modToC self.name

@[inline] def traceFile (self : Module) : FilePath :=
  self.pkg.modToTraceFile self.name

end Module

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

instance : ComputeHash OleanAndC IO := ⟨OleanAndC.computeHash⟩

protected def checkExists (self : OleanAndC) : BaseIO Bool := do
  return (← checkExists self.oleanFile) && (← checkExists self.cFile)

instance : CheckExists OleanAndC := ⟨OleanAndC.checkExists⟩

end OleanAndC

abbrev OleanAndCTarget := BuildTarget OleanAndC

namespace OleanAndCTarget

abbrev oleanFile (self : OleanAndCTarget) := self.info.oleanFile
def oleanTarget (self : OleanAndCTarget) : FileTarget :=
  Target.mk self.oleanFile do self.bindSync fun i _ => computeTrace i.oleanFile

abbrev cFile (self : OleanAndCTarget) := self.info.cFile
def cTarget (self : OleanAndCTarget) : FileTarget :=
  Target.mk self.cFile do self.bindSync fun i _ => computeTrace i.cFile

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

def OleanAndCTarget.activate (self : OleanAndCTarget) : SchedulerM ActiveOleanAndCTarget := do
  let t ← BuildTarget.activate self
  let oleanTask ← t.bindSync fun info depTrace => do
    return mixTrace (← computeTrace info.oleanFile) depTrace
  let cTask ← t.bindSync fun info _ => do
    return mixTrace (← computeTrace info.cFile) (← getLeanTrace)
  return t.withInfo {
    oleanTarget := ActiveTarget.mk self.oleanFile oleanTask
    cTarget := ActiveTarget.mk self.cFile cTask
  }

-- # Module Builders

def moduleTarget
[CheckExists i] [GetMTime i] [ComputeHash i m] [MonadLiftT m BuildM] (info : i)
(leanFile traceFile : FilePath) (contents : String) (depTarget : BuildTarget x)
(argTrace : BuildTrace) (build : BuildM PUnit) : BuildTarget i :=
  Target.mk info <| depTarget.bindOpaqueSync fun depTrace => do
    let srcTrace : BuildTrace := ⟨Hash.ofString contents, ← getMTime leanFile⟩
    let fullTrace := (← getLeanTrace).mix <| argTrace.mix <| srcTrace.mix depTrace
    let upToDate ← fullTrace.checkAgainstFile info traceFile
    unless upToDate do
      build
    fullTrace.writeToFile traceFile
    return depTrace

def moduleOleanAndCTarget
(leanFile cFile oleanFile traceFile : FilePath)
(contents : String)  (depTarget : BuildTarget x)
(rootDir : FilePath := ".") (leanArgs : Array String := #[]) : OleanAndCTarget :=
  let info := OleanAndC.mk oleanFile cFile
  let ileanFile := oleanFile.withExtension "ilean"
  moduleTarget info leanFile traceFile contents depTarget (pureHash leanArgs) do
    compileLeanModule leanFile oleanFile ileanFile cFile (← getOleanPath) rootDir leanArgs (← getLean)

def moduleOleanTarget
(leanFile oleanFile traceFile : FilePath)
(contents : String) (depTarget : BuildTarget x)
(rootDir : FilePath := ".") (leanArgs : Array String := #[]) : FileTarget :=
  let ileanFile := oleanFile.withExtension "ilean"
  let target := moduleTarget oleanFile leanFile traceFile contents depTarget (pureHash leanArgs) do
    compileLeanModule leanFile oleanFile ileanFile none (← getOleanPath) rootDir leanArgs (← getLean)
  target.withTask do target.bindSync fun oleanFile depTrace => do
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
(relative to the workspace).
-/
def recBuildModuleWithLocalImports
[Monad m] [MonadLiftT BuildM m] [MonadFunctorT BuildM m]
(build : Package → Name → FilePath → String → List α → BuildM α)
: RecBuild Module α m := fun info recurse => do
  have : MonadLift BuildM m := ⟨liftM⟩
  have : MonadFunctor BuildM m := ⟨fun f => monadMap (m := BuildM) f⟩
  let contents ← IO.FS.readFile info.srcFile
  let (imports, _, _) ← Elab.parseImports contents info.srcFile.toString
  -- we construct the import targets even if a rebuild is not required
  -- because other build processes (ex. `.o`) rely on the map being complete
  let importTargets ← imports.filterMapM fun imp => OptionT.run do
    let mod := imp.module
    let pkg ← OptionT.mk <| getPackageForModule? mod
    recurse ⟨pkg, mod⟩
  build info.pkg info.name info.srcFile contents importTargets

def recBuildModuleOleanAndCTargetWithLocalImports
[Monad m] [MonadLiftT BuildM m] [MonadFunctorT BuildM m] (depTarget : ActiveBuildTarget x)
: RecBuild Module ActiveOleanAndCTarget m :=
  recBuildModuleWithLocalImports fun pkg mod leanFile contents importTargets => do
    let importTarget ← ActiveTarget.collectOpaqueList <| importTargets.map (·.oleanTarget)
    let allDepsTarget := Target.active <| ← depTarget.mixOpaqueAsync importTarget
    pkg.moduleOleanAndCTargetOnly mod leanFile contents allDepsTarget |>.activate

def recBuildModuleOleanTargetWithLocalImports
[Monad m] [MonadLiftT BuildM m] [MonadFunctorT BuildM m] (depTarget : ActiveBuildTarget x)
: RecBuild Module ActiveFileTarget m :=
  recBuildModuleWithLocalImports fun pkg mod leanFile contents importTargets => do
    let importTarget ← ActiveTarget.collectOpaqueList importTargets
    let allDepsTarget := Target.active <| ← depTarget.mixOpaqueAsync importTarget
    pkg.moduleOleanTargetOnly mod leanFile contents allDepsTarget |>.activate

-- ## Definitions

abbrev ModuleBuildM (α) :=
  -- equivalent to `RBTopT (cmp := Name.quickCmp) Name α BuildM`.
  -- phrased this way to use `NameMap`
  EStateT (List Name) (NameMap α) BuildM

abbrev RecModuleBuild (o) :=
  RecBuild Module o (ModuleBuildM o)

abbrev RecModuleTargetBuild (i) :=
  RecModuleBuild (ActiveBuildTarget i)

-- ## Builders

/-- Build a single module using the recursive module build function `build`. -/
def buildModule (mod : Module)
[Inhabited o] (build : RecModuleBuild o) : BuildM o := do
  failOnBuildCycle <| ← RBTopT.run' do
    buildRBTop (cmp := Name.quickCmp) build Module.name mod

/--
Build each module using the recursive module function `build`,
constructing an `Array`  of the results.
-/
def buildModuleArray (mods : Array Module)
[Inhabited o] (build : RecModuleBuild o) : BuildM (Array o) := do
  failOnBuildCycle <| ← RBTopT.run' <| mods.mapM <|
    buildRBTop (cmp := Name.quickCmp) build Module.name

/--
Build each module using the recursive module function `build`,
constructing a module-target `NameMap`  of the results.
-/
def buildModuleMap [Inhabited o]
(infos : Array Module) (build : RecModuleBuild o)
: BuildM (NameMap o) := do
  let (x, objMap) ← RBTopT.run do
    infos.forM fun info => discard <| buildRBTop build Module.name info
  failOnBuildCycle x
  return objMap
