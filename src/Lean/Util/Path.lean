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

@[export lean_get_prefix]
def getBuildDir : IO FilePath := do
  return (← IO.appDir).parent |>.get!

@[export lean_get_libdir]
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

def getSrcSearchPath : IO SearchPath := do
  let srcSearchPath := (← IO.getEnv "LEAN_SRC_PATH")
    |>.map System.SearchPath.parse
    |>.getD []
  let srcPath := (← IO.appDir) / ".." / "src" / "lean"
  -- `lake/` should come first since on case-insensitive file systems, Lean thinks that `src/` also contains `Lake/`
  return srcSearchPath ++ [srcPath / "lake", srcPath]

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
  let modNameStr := FilePath.mk fnameSuffix |>.withExtension ""
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
  return out.trim

end Lean
