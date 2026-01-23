/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

Management of the Lean search path (`LEAN_PATH`), which is a list of
paths containing package roots: an import `A.B.C` resolves to
`path/A/B/C.olean` for the first entry `path` in `LEAN_PATH`
with a directory `A/`. `import A` resolves to `path/A.olean`.
-/
module

prelude
public import Init.System.IO
import Init.Data.ToString.Name
import Init.Data.String.TakeDrop
public import Lean.Data.NameMap.Basic
import Lean.Data.Json.Parser
public import Std.Sync.Mutex
public import Lean.Util.PkgId
import Lean.Data.Json.Printer

public section

namespace Lean
open System

/--
Executes `f` with the corresponding module name for each `.lean` file contained in `dir`.

For example, if `dir` contains `A/B/C.lean`, `f` is called with `A.B.C`.
-/
partial def forEachModuleInDir [Monad m] [MonadLiftT IO m]
    (dir : FilePath) (f : Lean.Name → m PUnit) : m PUnit := do
  for entry in (← dir.readDir) do
    if (← liftM (m := IO) <| entry.path.isDir) then
      let n := Lean.Name.mkSimple entry.fileName
      forEachModuleInDir entry.path (f <| n ++ ·)
    else if entry.path.extension == some "lean" then
      f <| Lean.Name.mkSimple <| FilePath.withExtension entry.fileName "" |>.toString

def realPathNormalized (p : FilePath) : IO FilePath :=
  return (← IO.FS.realPath p).normalize

def modToFilePath (base : FilePath) (mod : Name) (ext : String) : FilePath :=
  go mod |>.addExtension ext
where
  go : Name → FilePath
  | Name.str p h => go p / h
  | Name.anonymous => base
  | Name.num _ _ => panic! "ill-formed import"

/-- A `.olean' search path. -/
abbrev SearchPath := System.SearchPath

namespace SearchPath

/-- If the package of `mod` can be found in `sp`, return the path with extension
`ext` (`lean` or `olean`) corresponding to `mod`. Otherwise, return `none`. Does
not check whether the returned path exists. -/
def findWithExt (sp : SearchPath) (ext : String) (mod : Name) : IO (Option FilePath) := do
  let pkg := mod.getRoot.toString (escape := false)
  let root? ← sp.findM? fun p =>
    (p / pkg).isDir <||> ((p / pkg).addExtension ext).pathExists
  return root?.map (modToFilePath · mod ext)

/-- Like `findWithExt`, but ensures the returned path exists. -/
def findModuleWithExt (sp : SearchPath) (ext : String) (mod : Name) : IO (Option FilePath) := do
  if let some path ← findWithExt sp ext mod then
    if ← path.pathExists then
      return some path
  return none

def findAllWithExt (sp : SearchPath) (ext : String) : IO (Array FilePath) := do
  let mut paths := #[]
  for p in sp do
    if (← p.isDir) then
      paths := paths ++ (← p.walkDir).filter (·.extension == some ext)
  return paths

end SearchPath

builtin_initialize searchPathRef : IO.Ref SearchPath ← IO.mkRef {}

def getBuildDir : IO FilePath := do
  return (← IO.appDir).parent |>.get!

def getLibDir (leanSysroot : FilePath) : IO FilePath := do
  let mut buildDir := leanSysroot
  -- use stage1 stdlib with stage0 executable (which should never be distributed outside of the build directory)
  if Internal.isStage0 () then
    buildDir := buildDir / ".." / "stage1"
  return buildDir / "lib" / "lean"

def getBuiltinSearchPath (leanSysroot : FilePath) : IO SearchPath :=
  return [← getLibDir leanSysroot]

def addSearchPathFromEnv (sp : SearchPath) : IO SearchPath := do
  let val ← IO.getEnv "LEAN_PATH"
  match val with
  | none     => pure sp
  | some val => pure <| SearchPath.parse val ++ sp

/--
Initialize Lean's search path given Lean's system root and an initial search path.
The system root can be obtained via `getBuildDir` (for internal use) or
`findSysroot` (for external users). -/
def initSearchPath (leanSysroot : FilePath) (sp : SearchPath := ∅) : IO Unit := do
  let sp := sp ++ (← addSearchPathFromEnv (← getBuiltinSearchPath leanSysroot))
  searchPathRef.set sp

@[export lean_init_search_path]
private def initSearchPathInternal : IO Unit := do
  initSearchPath (← getBuildDir)

/-- Find the compiled `.olean` of a module in the `LEAN_PATH` search path. -/
partial def findOLean (mod : Name) : IO FilePath := do
  let sp ← searchPathRef.get
  if let some fname ← sp.findWithExt "olean" mod then
    return fname
  else
    let pkg := FilePath.mk <| mod.getRoot.toString (escape := false)
    throw <| IO.userError s!"unknown module prefix '{pkg}'\n\n\
      No directory '{pkg}' or file '{pkg}.olean' in the search path entries:\n\
      {"\n".intercalate <| sp.map (·.toString)}"

/-- Find the `.lean` source of a module in a `LEAN_SRC_PATH` search path. -/
partial def findLean (sp : SearchPath) (mod : Name) : IO FilePath := do
  if let some fname ← sp.findWithExt "lean" mod then
    return fname
  else
    let pkg := FilePath.mk <| mod.getRoot.toString (escape := false)
    throw <| IO.userError s!"unknown module prefix '{pkg}'\n\n\
      No directory '{pkg}' or file '{pkg}.lean' in the search path entries:\n\
      {"\n".intercalate <| sp.map (·.toString)}"

/-- Infer module name of source file name. -/
def moduleNameOfFileName (fname : FilePath) (rootDir : Option FilePath) : IO Name := do
  let fname ← IO.FS.realPath fname
  let rootDir ← match rootDir with
    | some rootDir => pure rootDir
    | none         => IO.currentDir
  let mut rootDir ← realPathNormalized rootDir
  if !rootDir.toString.endsWith System.FilePath.pathSeparator.toString then
    rootDir := ⟨rootDir.toString ++ System.FilePath.pathSeparator.toString⟩
  if !rootDir.toString.isPrefixOf fname.normalize.toString then
    throw $ IO.userError s!"input file '{fname}' must be contained in root directory ({rootDir})"
  -- NOTE: use `fname` instead of `fname.normalize` to preserve casing on all platforms
  let fnameSuffix := fname.toString.drop rootDir.toString.length
  let modNameStr := FilePath.mk fnameSuffix.copy |>.withExtension ""
  let modName    := modNameStr.components.foldl Name.mkStr Name.anonymous
  pure modName

def searchModuleNameOfFileName (fname : FilePath) (rootDirs : SearchPath) : IO (Option Name) := do
  for rootDir in rootDirs do
    try
      return some <| ← moduleNameOfFileName fname <| some rootDir
    catch
      -- Try the next one
      | _ => pure ()
  return none

abbrev PkgContext.PkgSourceRoots := NameMap System.FilePath
/-- Package => Module prefix => Source root path -/
abbrev PkgContext.SourceRoots := Std.TreeMap VersionedPkgId PkgSourceRoots

/--
Dependency closure of any given package in a workspace.
Note that in multi-version workspaces, the immediate depends-on relation is not transitive:
```
  --> B --> D (version 1)
 /
A
 \
  --> C -->[only private] D (version 2)
```
Here, C depends on D (version 2) and B depends on D (version 1),
while A depends on B, C and D (version 1).
Specifically, A does not depend on D (version 2).
-/
structure PkgContext.Dependencies where
  dependsOn : Std.TreeMap VersionedPkgId (Std.TreeSet VersionedPkgId) := {}
  dependedOnBy : Std.TreeMap VersionedPkgId (Std.TreeSet VersionedPkgId) := {}
  deriving Inhabited, Repr

structure PkgContext where
  sourceRoots : PkgContext.SourceRoots := {}
  dependencies : PkgContext.Dependencies := {}
  deriving Inhabited, Repr

namespace PkgContext

def ofEnvVarContent (var : String) : PkgContext := Id.run do
  -- TODO: define
  let .ok (.obj envVarObj) := Json.parse var
    | panic! "PkgSourceRoots.ofEnvVar: Cannot parse LEAN_PKG_CTX environment variable"
  let some (.obj sourceRootsObj) := envVarObj.get? "sourceRoots"
    | panic! "PkgSourceRoots.ofEnvVar: Cannot parse 'sourceRoots' field in LEAN_PKG_CTX environment variable"
  let some (.obj dependenciesObj) := envVarObj.get? "dependencies"
    | panic! "PkgSourceRoots.ofEnvVar: Cannot parse 'dependencies' field in LEAN_PKG_CTX environment variable"

  let mut sourceRoots : SourceRoots := {}
  for (k, v) in sourceRootsObj do
    let pkgId := k
    let .obj pkgSourceRootsObj := v
      | panic! s!"PkgSourceRoots.ofEnvVar: Cannot parse source roots of package '{k}' in LEAN_PKG_CTX environment variable"
    let mut pkgSourceRoots : PkgSourceRoots := {}
    for (k, v) in pkgSourceRootsObj do
      let modulePrefix := k.toName
      let .str path := v
        | panic! s!"PkgSourceRoots.ofEnvVar: Cannot parse path of package '{k}' in LEAN_PKG_CTX environment variable"
      pkgSourceRoots := pkgSourceRoots.insert modulePrefix path
    sourceRoots := sourceRoots.insert pkgId pkgSourceRoots

  let mut dependsOn : Std.TreeMap VersionedPkgId (Std.TreeSet VersionedPkgId) := {}
  let mut dependedOnBy : Std.TreeMap VersionedPkgId (Std.TreeSet VersionedPkgId) := {}
  for (k, v) in dependenciesObj do
    let pkgId := k
    let .arr depsArr := v
      | panic! s!"PkgSourceRoots.ofEnvVar: Cannot parse dependencies of package '{k}' in LEAN_PKG_CTX environment variable"
    let deps := depsArr.map fun dep => Id.run do
      let .str dep := dep
        | panic! s!"PkgSourceRoots.ofEnvVar: Cannot parse a dependency of package '{k}' in LEAN_PKG_CTX environment variable"
      return dep
    let deps := Std.TreeSet.ofArray deps |>.insert pkgId
    dependsOn := dependsOn.insert pkgId deps
    for dep in deps do
      dependedOnBy := dependedOnBy.alter dep fun
        | none => some { pkgId }
        | some inverseDeps => some <| inverseDeps.insert pkgId

  return {
    sourceRoots
    dependencies := { dependsOn, dependedOnBy }
  }

def ofEnvVar : BaseIO PkgContext := do
  -- TODO: define
  let some var ← IO.getEnv "LEAN_PKG_CTX"
    | return {}
  return ofEnvVarContent var

def formatEnvVar
    (sourceRoots : Std.TreeMap VersionedPkgId PkgSourceRoots)
    (dependencies : Std.TreeMap VersionedPkgId (Array VersionedPkgId)) :
    String := Id.run do
  let mut sourceRootsObj : Std.TreeMap.Raw String Json := ∅
  for (pkg, roots) in sourceRoots do
    let mut pkgSourceRootsObj : Std.TreeMap.Raw String Json := ∅
    for (modPrefix, path) in roots do
      pkgSourceRootsObj := pkgSourceRootsObj.insert modPrefix.toString (.str path.toString)
    sourceRootsObj := sourceRootsObj.insert pkg (.obj pkgSourceRootsObj)
  let mut dependenciesObj : Std.TreeMap.Raw String Json := ∅
  for (pkg, deps) in dependencies do
    let depsArr := deps.map Json.str
    dependenciesObj := dependenciesObj.insert pkg (.arr depsArr)
  let mut envVarObj : Std.TreeMap.Raw String Json := Std.TreeMap.Raw.ofArray #[
    ("sourceRoots", Json.obj sourceRootsObj),
    ("dependencies", Json.obj dependenciesObj)
  ]
  return Json.compress (.obj envVarObj)

partial def transitivelyDependsOn (c : PkgContext) (pkg? : Option VersionedPkgId) : Std.TreeSet VersionedPkgId := Id.run do
  let some pkg := pkg?
    | return { .core }
  return c.dependencies.dependsOn.getD pkg {}

partial def transitivelyDependedOnBy (c : PkgContext) (pkg : VersionedPkgId) : Std.TreeSet VersionedPkgId := Id.run do
  return c.dependencies.dependedOnBy.getD pkg {}

def isVisible (c : PkgContext) (pkg1? pkg2? : Option VersionedPkgId) : Bool := Id.run do
  let (some pkg1, some pkg2) := (pkg1?, pkg2?)
    | return pkg1? == pkg2?
  pkg1 == pkg1
    || (c.transitivelyDependsOn pkg1 |>.contains pkg2)
    || (c.transitivelyDependsOn pkg2 |>.contains pkg1)

def modToPath'? (c : PkgContext) (modId : GlobalModId) : Option FilePath := do
  -- We assume that module prefixes are disjoint in a given dependency closure.
  -- Otherwise, modules (even within a single package) cannot be resolved to a unique path:
  -- Consider `Foo.Bar => /Foo` and `Foo => /Bar` with files `/Foo/Bar/Foobar.lean` and
  -- `/Bar/Foobar.lean`, both of which resolve to the same module name `Foo.Bar.Foobar`.
  let depClosure := c.transitivelyDependsOn modId.pkg?
  for pkg in depClosure do
    let some pkgSourceRoots := c.sourceRoots.get? pkg
      | continue
    for (modulePrefix, rootPath) in pkgSourceRoots do
      if modulePrefix.isPrefixOf modId.mod then
        let relativeMod := modId.mod.replacePrefix modulePrefix .anonymous
        return modToFilePath rootPath relativeMod "lean"
  none

def pathToMod'? (c : PkgContext) (path : FilePath) : Option GlobalModId := do
  -- We assume that root paths are disjoint in all packages of a project.
  let some path := path.normalize.toString.dropSuffix? ".lean"
    | panic! "`PkgContext.pathToMod?`: Expected `.lean` path."
  for (pkg, pkgSourceRoots) in c.sourceRoots do
    for (modulePrefix, rootPath) in pkgSourceRoots do
      let mut rootPath := rootPath.toString
      if rootPath == path then
        -- `/Foo/Bar.lean` belongs to a root path of `/Foo/Bar`
        return { pkg? := pkg, mod := modulePrefix }
      if ! rootPath.endsWith FilePath.pathSeparator then
        -- Ensure that `/Foo/Bar` does not match `Foo/Barf/Foobar.lean`
        rootPath := rootPath.push FilePath.pathSeparator
      let some relativePath := path.dropPrefix? rootPath
        | continue
      return {
        pkg? := pkg
        mod := relativePath.toString |> FilePath.mk |>.components.foldl Name.mkStr modulePrefix
      }
  none

private builtin_initialize pkgContextMutex : Std.Mutex (Option PkgContext) ← Std.Mutex.new none

/--
Multi-version workspace compatible version of the legacy source search path.
Allows converting between source file paths and module names in the dependency closure of a specific
package.
See also `getSrcSearchPath`.
-/
def getPkgContext : BaseIO PkgContext := do
  pkgContextMutex.atomically do
    if let some pkgContext ← get then
      return pkgContext
    let pkgContext ← PkgContext.ofEnvVar
    set <| some pkgContext
    return pkgContext

def modToPath? (modId : GlobalModId) : BaseIO (Option FilePath) := do
  let c ← getPkgContext
  return modToPath'? c modId

def pathToMod? (path : FilePath) : BaseIO (Option GlobalModId) := do
  let c ← getPkgContext
  return pathToMod'? c path

end PkgContext

/--
Overrides the `LEAN_SRC_PATH` field in `getSrcSearchPath`.
Used by the file worker process of the language server to set a source path for that
specific file.
-/
private builtin_initialize currentPackageSourcePathRef : IO.Ref (Option SearchPath) ← IO.mkRef none

def initCurrentPackageSourcePath (currentPackageSourcePath : SearchPath) : IO Unit := do
  currentPackageSourcePathRef.set <| some currentPackageSourcePath

/--
Legacy source search path.
When multi-version workspaces are not enabled, this source search path is equivalent to
`getPkgContext`.
When multi-version workspaces are enabled in a package, the legacy source search path must be used
with care:
- In the dependency closure of a given package, module names uniquely identify source files on disk,
  so the legacy source search path works as expected.
  - Lake ensures that the source search path is set correctly when in the context of a specific
    package.
  - The language server ensures that it is set correctly for the current file during elaboration.
- When working with the entire workspace (e.g. in the language server), the legacy source search
  path is not sufficient to convert from module names to file paths anymore, as module names do not
  uniquely identify source files at a global level. In this kind of context, `getPkgContext` must
  be used instead.
-/
def getSrcSearchPath : IO SearchPath := do
  if let some srcSearchPath ← currentPackageSourcePathRef.get then
    return srcSearchPath
  let srcSearchPath := (← IO.getEnv "LEAN_SRC_PATH")
    |>.map System.SearchPath.parse
    |>.getD []
  let srcPath := (← IO.appDir) / ".." / "src" / "lean"
  -- `lake/` should come first since on case-insensitive file systems, Lean thinks that `src/` also contains `Lake/`
  return srcSearchPath ++ [srcPath / "lake", srcPath]

/--
  Find the system root of the given `lean` command
  by calling `lean --print-prefix` and returning the path it prints.
  Defaults to trying the `lean` in `PATH`.
  If set, the `LEAN_SYSROOT` environment variable takes precedence.
  Note that the called `lean` binary might not be part of the system root,
  e.g. in the case of `elan`'s proxy binary.
  Users internal to Lean should use `Lean.getBuildDir` instead.
-/
def findSysroot (lean := "lean") : IO FilePath := do
  if let some root ← IO.getEnv "LEAN_SYSROOT" then
    return root
  let out ← IO.Process.run {
    cmd := lean
    args := #["--print-prefix"]
  }
  return out.trimAscii.copy

end Lean
