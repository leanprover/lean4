/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Config.LeanLib

namespace Lake
open Lean System

/-- A buildable Lean module of a `LeanLib`. -/
public structure Module where
  lib : LeanLib
  name : Name

@[deprecated name (since := "2025-11-13")]
public abbrev Module.keyName := name

public instance : ToJson Module := ⟨(toJson ·.name)⟩
public instance : ToString Module := ⟨(·.name.toString)⟩

public instance : Hashable Module where hash m := hash m.name
public instance : BEq Module where beq m n := m.name == n.name

public abbrev ModuleSet := Std.HashSet Module
@[inline] public def ModuleSet.empty : ModuleSet := ∅

public abbrev OrdModuleSet := OrdHashSet Module
@[inline] public def OrdModuleSet.empty : OrdModuleSet := OrdHashSet.empty

public abbrev ModuleMap (α) := Std.TreeMap Module α (·.name.quickCmp ·.name)
@[inline] public def ModuleMap.empty : ModuleMap α := Std.TreeMap.empty

/--
Locate the named, buildable module in the library
(which implies it is local and importable).
-/
public def LeanLib.findModule? (mod : Name) (self : LeanLib) : Option Module :=
  if self.isBuildableModule mod then some {lib := self, name := mod} else none

/--
Returns the buildable module in the library whose source file or directory is `path`.

For example, in a library with a source directory of `src`,
`src/Foo/Bar.lean` and `src/Foo/Bar/` will both resolve to the module `Foo.Bar`.
-/
public def LeanLib.findModuleBySrc? (path : FilePath) (self : LeanLib) : Option Module := do
  let modPath ← path.toString.dropPrefix? self.srcDir.toString
  let modPath := (modPath.drop 1).toString -- remove leading `/`
  let modPath ← modPath.dropSuffix? ".lean" <|> modPath.dropSuffix? FilePath.pathSeparator.toString
  let modName := FilePath.components modPath.toString |>.foldl .str .anonymous
  self.findModule? modName

/-- Locate the named, buildable, importable, local module in the package.  -/
public def Package.findModule? (mod : Name) (self : Package) : Option Module :=
  self.leanLibs.findSomeRev? (·.findModule? mod)

/-- Get an `Array` of the library's modules (as specified by its globs). -/
public def LeanLib.getModuleArray (self : LeanLib) : IO (Array Module) :=
  (·.2) <$> StateT.run (s := #[]) do
    self.config.globs.forM fun glob => do
      glob.forEachModuleIn self.srcDir fun mod => do
        modify (·.push {lib := self, name := mod})

/-- The library's buildable root modules. -/
public def LeanLib.rootModules (self : LeanLib) : Array Module :=
  self.config.roots.filterMap self.findModule?

namespace Module

public abbrev pkg (self : Module) : Package :=
  self.lib.pkg

@[inline] public def rootDir (self : Module) : FilePath :=
  self.lib.rootDir

@[inline] public def filePath (dir : FilePath) (ext : String) (self : Module) : FilePath :=
  Lean.modToFilePath dir self.name ext

@[inline] public def srcPath (ext : String) (self : Module) : FilePath :=
  self.filePath self.lib.srcDir ext

@[inline] public def leanFile (self : Module) : FilePath :=
  self.srcPath "lean"

@[inline] public def relLeanFile (self : Module) : FilePath :=
  relPathFrom self.pkg.dir self.leanFile

@[inline] public def leanLibPath (ext : String) (self : Module) : FilePath :=
  self.filePath self.pkg.leanLibDir ext

@[inline] public def oleanFile (self : Module) : FilePath :=
  self.leanLibPath "olean"

@[inline] public def oleanServerFile (self : Module) : FilePath :=
  self.leanLibPath "olean.server"

@[inline] public def oleanPrivateFile (self : Module) : FilePath :=
  self.leanLibPath "olean.private"

@[inline] public def ileanFile (self : Module) : FilePath :=
  self.leanLibPath "ilean"

@[inline] public def traceFile (self : Module) : FilePath :=
  self.leanLibPath "trace"

@[inline] public def irPath (ext : String) (self : Module) : FilePath :=
  self.filePath self.pkg.irDir ext

@[inline] public def setupFile (self : Module) : FilePath :=
  self.irPath "setup.json"

@[inline] public def irFile (self : Module) : FilePath :=
  self.leanLibPath "ir"

@[inline] public def cFile (self : Module) : FilePath :=
  self.irPath "c"

@[inline] public def coExportFile (self : Module) : FilePath :=
  self.irPath "c.o.export"

@[inline] public def coNoExportFile (self : Module) : FilePath :=
  self.irPath "c.o.noexport"

@[inline] public def bcFile (self : Module) : FilePath :=
  self.irPath "bc"

public def bcFile? (self : Module) : Option FilePath :=
  if Lean.Internal.hasLLVMBackend () then some self.bcFile else none

@[inline] public def bcoFile (self : Module) : FilePath :=
  self.irPath "bc.o"

/-- Suffix for single module dynlibs (e.g., for precompilation). -/
public def dynlibSuffix := "-1"

@[inline] public def dynlibName (self : Module) : String :=
  /-
  * File name MUST be unique on Windows
  * Uses the mangled module name so the library name matches the
    name used for the module's initialization function, thus enabling it
    to be loaded as a plugin.
  -/
  mkModuleInitializationStem self.name self.pkg.id?

@[inline] public def dynlibFile (self : Module) : FilePath :=
  self.pkg.leanLibDir / s!"{self.dynlibName}.{sharedLibExt}"

@[inline] public def serverOptions (self : Module) : LeanOptions :=
  self.lib.serverOptions

@[inline] public def buildType (self : Module) : BuildType :=
  self.lib.buildType

@[inline] public def backend (self : Module) : Backend :=
  self.lib.backend

@[inline] public def allowImportAll (self : Module) : Bool :=
  self.lib.allowImportAll

@[inline] public def dynlibs (self : Module) : TargetArray Dynlib :=
  self.lib.dynlibs

@[inline] public def plugins (self : Module) : TargetArray Dynlib :=
  self.lib.plugins

@[inline] public def leanOptions (self : Module) : LeanOptions :=
  self.lib.leanOptions

@[inline] public def leanArgs (self : Module) : Array String :=
  self.lib.leanArgs

@[inline] public def weakLeanArgs (self : Module) : Array String :=
  self.lib.weakLeanArgs

@[inline] public def leancArgs (self : Module) : Array String :=
  self.lib.leancArgs

@[inline] public def weakLeancArgs (self : Module) : Array String :=
  self.lib.weakLeancArgs

@[inline] public def linkArgs (self : Module) : Array String :=
  self.lib.linkArgs

@[inline] public def weakLinkArgs (self : Module) : Array String :=
  self.lib.weakLinkArgs

@[inline] public def leanIncludeDir? (self : Module) : Option FilePath :=
  if self.pkg.bootstrap then some <| self.pkg.buildDir / "include" else none

@[inline] public def platformIndependent (self : Module) : Option Bool :=
  self.lib.platformIndependent

@[inline] public def shouldPrecompile (self : Module) : Bool :=
  self.lib.precompileModules

@[inline] public def nativeFacets (self : Module) (shouldExport : Bool) : Array (ModuleFacet FilePath) :=
  self.lib.nativeFacets shouldExport

/-! ## Trace Helpers -/

public protected def getMTime (self : Module) : IO MTime := do
  return mixTrace (mixTrace (← getMTime self.oleanFile) (← getMTime self.ileanFile)) (← getMTime self.cFile)

public instance : GetMTime Module := ⟨Module.getMTime⟩

public protected def checkExists (self : Module) : BaseIO Bool := do
  let bcFileExists? ←
    if Lean.Internal.hasLLVMBackend () then
      checkExists self.bcFile
    else
      pure true
  return (← checkExists self.oleanFile) && (← checkExists self.ileanFile) && (← checkExists self.cFile) && bcFileExists?

public instance : CheckExists Module := ⟨Module.checkExists⟩
