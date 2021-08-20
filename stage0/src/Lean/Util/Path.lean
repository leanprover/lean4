/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

Management of the Lean search path (`LEAN_PATH`), which is a list of
paths containing package roots: an import `A.B.C` resolves to
`path/A/B/C.olean` for the first entry `path` in `LEAN_PATH`
with a directory `A/`. `import A` resolves to `path/A.olean`.
-/
import Lean.Data.Name

namespace Lean
open System

def realPathNormalized (p : FilePath) : IO FilePath := do
  (← IO.FS.realPath p).normalize

def modToFilePath (base : FilePath) (mod : Name) (ext : String) : FilePath :=
  go mod |>.withExtension ext
where
  go : Name → FilePath
  | Name.str p h _ => go p / h
  | Name.anonymous => base
  | Name.num p _ _ => panic! "ill-formed import"

/-- A `.olean' search path. -/
abbrev SearchPath := System.SearchPath

namespace SearchPath

/-- If the package of `mod` can be found in `sp`, return the path with extension
`ext` (`lean` or `olean`) corresponding to `mod`. Otherwise, return `none.` -/
def findWithExt (sp : SearchPath) (ext : String) (mod : Name) : IO (Option FilePath) := do
  let pkg := mod.getRoot.toString
  let root? ← sp.findM? fun p =>
    (p / pkg).isDir <||> ((p / pkg).withExtension ext).pathExists
  return root?.map (modToFilePath · mod ext)

end SearchPath

builtin_initialize searchPathRef : IO.Ref SearchPath ← IO.mkRef {}

@[extern c inline "LEAN_IS_STAGE0"]
private constant isStage0 (u : Unit) : Bool

@[export lean_get_prefix]
def getBuildDir : IO FilePath := do
  return (← IO.appDir).parent |>.get!

@[export lean_get_libdir]
def getLibDir : IO FilePath := do
  let mut buildDir ← getBuildDir
  -- use stage1 stdlib with stage0 executable (which should never be distributed outside of the build directory)
  if isStage0 () then
    buildDir := buildDir / ".." / "stage1"
  buildDir / "lib" / "lean"

def getBuiltinSearchPath : IO SearchPath :=
  return [← getLibDir]

def addSearchPathFromEnv (sp : SearchPath) : IO SearchPath := do
  let val ← IO.getEnv "LEAN_PATH"
  match val with
  | none     => pure sp
  | some val => pure <| SearchPath.parse val ++ sp

@[export lean_init_search_path]
def initSearchPath (path : Option String := none) : IO Unit :=
  match path with
  | some path => searchPathRef.set <| SearchPath.parse path
  | none      => do
    let sp ← getBuiltinSearchPath
    let sp ← addSearchPathFromEnv sp
    searchPathRef.set sp

partial def findOLean (mod : Name) : IO FilePath := do
  let sp ← searchPathRef.get
  if let some fname ← sp.findWithExt "olean" mod then
    return fname
  else
    let pkg := FilePath.mk mod.getRoot.toString
    let mut msg := s!"unknown package '{pkg}'"
    let rec maybeThisOne dir := do
      if ← (dir / pkg).isDir then
        return some s!"\nYou might need to open '{dir}' as a workspace in your editor"
      if let some dir ← dir.parent then
        maybeThisOne dir
      else
       return none
    if let some msg' ← maybeThisOne (← IO.currentDir) then
      msg := msg ++ msg'
    throw <| IO.userError msg

/-- Infer module name of source file name. -/
@[export lean_module_name_of_file]
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

end Lean
