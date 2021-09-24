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

structure OleanAndC where
  oleanFile : FilePath
  cFile : FilePath
  deriving Inhabited

namespace OleanAndC

protected def getMTime (self : OleanAndC) : IO MTime := do
  return mixTrace (← getMTime self.oleanFile) (← getMTime self.cFile)

instance : GetMTime OleanAndC := ⟨OleanAndC.getMTime⟩

protected def computeHash (self : OleanAndC) : IO Hash := do
  return mixTrace (← computeHash self.oleanFile) (← computeHash self.cFile)

instance : ComputeHash OleanAndC := ⟨OleanAndC.computeHash⟩

end OleanAndC

abbrev ActiveOleanAndCTarget := ActiveBuildTarget OleanAndC

namespace ActiveOleanAndCTarget

def oleanFile (self : ActiveOleanAndCTarget) := self.info.oleanFile
def oleanTarget (self : ActiveOleanAndCTarget) : ActiveFileTarget :=
  self.withInfo self.oleanFile

def cFile (self : ActiveOleanAndCTarget) := self.info.cFile
def cTarget (self : ActiveOleanAndCTarget) : ActiveFileTarget :=
  self.withInfo self.cFile

end ActiveOleanAndCTarget

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

def moduleTarget [GetMTime i] [ComputeHash i] (info : i)
(leanFile hashFile : FilePath) (contents : String) (depTarget : BuildTarget x)
(build : BuildM PUnit) : BuildTarget i :=
  Target.mk info <| depTarget.mapOpaqueAsync fun depTrace => do
    let (upToDate, trace) ← checkModuleTrace info leanFile hashFile contents depTrace
    if upToDate then
      BuildTrace.fromHash <| (← computeHash info).mix depTrace.hash
    else
      build
      IO.FS.writeFile hashFile trace.hash.toString
      let newTrace : BuildTrace ← liftM <| computeTrace info
      newTrace.mix depTrace

def moduleOleanAndCTarget
(leanFile cFile oleanFile hashFile : FilePath)
(oleanDirs : List FilePath) (contents : String)  (depTarget : BuildTarget x)
(rootDir : FilePath := ".") (leanArgs : Array String := #[]) :=
  moduleTarget (OleanAndC.mk oleanFile cFile) leanFile hashFile contents depTarget <|
    compileOleanAndC leanFile oleanFile cFile oleanDirs rootDir leanArgs

def moduleOleanTarget
(leanFile oleanFile hashFile : FilePath)
(oleanDirs : List FilePath) (contents : String) (depTarget : BuildTarget x)
(rootDir : FilePath := ".") (leanArgs : Array String := #[]) :=
  moduleTarget oleanFile leanFile hashFile contents depTarget <|
    compileOlean leanFile oleanFile oleanDirs rootDir leanArgs

protected def Package.moduleOleanAndCTarget
(self : Package) (moreOleanDirs : List FilePath) (mod : Name)
(leanFile : FilePath) (contents : String) (depTarget : BuildTarget x) :=
  let cFile := self.modToC mod
  let oleanFile := self.modToOlean mod
  let hashFile := self.modToHashFile mod
  let oleanDirs :=  self.oleanDir :: moreOleanDirs
  moduleOleanAndCTarget leanFile cFile oleanFile hashFile oleanDirs contents
    depTarget self.rootDir self.leanArgs

protected def Package.moduleOleanTarget
(self : Package) (moreOleanDirs : List FilePath) (mod : Name)
(leanFile : FilePath) (contents : String) (depTarget : BuildTarget x) :=
  let oleanFile := self.modToOlean mod
  let hashFile := self.modToHashFile mod
  let oleanDirs := self.oleanDir :: moreOleanDirs
  moduleOleanTarget leanFile oleanFile hashFile oleanDirs contents depTarget
    self.rootDir self.leanArgs

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
  let imports := imports.map (·.module) |>.filter pkg.isLocalModule
  -- we fetch the import targets even if a rebuild is not required
  -- because other build processes (ex. `.o`) rely on the map being complete
  let importTargets ← imports.mapM fetch
  build mod leanFile contents importTargets

def Package.recFetchModuleOleanAndCTargetWithLocalImports [Monad m] [MonadLiftT BuildM m]
(self : Package) (moreOleanDirs : List FilePath) (depTarget : ActiveBuildTarget x)
: RecFetch Name ActiveOleanAndCTarget m :=
  recFetchModuleWithLocalImports self fun mod leanFile contents importTargets => do
    let allDepsTarget := Target.active <| ←
      depTarget.mixOpaqueAsync <| ← ActiveTarget.collectOpaqueList importTargets
    self.moduleOleanAndCTarget moreOleanDirs mod leanFile contents allDepsTarget |>.run

def  Package.recFetchModuleOleanTargetWithLocalImports [Monad m] [MonadLiftT BuildM m]
(self : Package) (moreOleanDirs : List FilePath) (depTarget : ActiveBuildTarget x)
: RecFetch Name ActiveFileTarget m :=
  recFetchModuleWithLocalImports self fun mod leanFile contents importTargets => do
    let allDepsTarget := Target.active <| ←
      depTarget.mixOpaqueAsync <| ← ActiveTarget.collectOpaqueList importTargets
    self.moduleOleanTarget moreOleanDirs mod leanFile contents allDepsTarget |>.run

-- ## Definitions

abbrev ModuleFetchM (α) :=
  -- equivalent to `RBTopT (cmp := Name.quickCmp) Name α BuildM`.
  -- phrased this way to use `NameMap`
  EStateT (List Name) (NameMap α) BuildM

abbrev ModuleFetch (α) :=
  RecFetch Name α (ModuleFetchM α)

abbrev OleanTargetFetch := ModuleFetch ActiveFileTarget
abbrev OleanAndCTargetFetch := ModuleFetch ActiveOleanAndCTarget

abbrev OleanTargetMap := NameMap ActiveFileTarget
abbrev OleanAndCTargetMap := NameMap ActiveOleanAndCTarget
