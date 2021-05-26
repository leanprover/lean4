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

def realPathNormalized (p : FilePath) : IO String := do
  (← IO.realPath p).normalize

def modPathToFilePath : Name → FilePath
  | Name.str p h _              => modPathToFilePath p / h
  | Name.anonymous              => ""
  | Name.num p _ _              => panic! "ill-formed import"

abbrev SearchPath := List FilePath

namespace SearchPath

/-- If the package of `mod` can be found in `sp`, return the path with extension
`ext` (`.lean` or `.olean`) corresponding to `mod`. Otherwise, return `none.` -/
def findWithExt (sp : SearchPath) (ext : String) (mod : Name) : IO (Option FilePath) := do
  let pkg := mod.getRoot.toString
  let root? ← sp.findM? fun p =>
    (p / pkg).isDir <||> (p / (pkg ++ ext)).pathExists
  return root?.map (· ++ modPathToFilePath mod ++ ext)

end SearchPath

builtin_initialize searchPathRef : IO.Ref SearchPath ← IO.mkRef {}

def parseSearchPath (path : String) (sp : SearchPath := ∅) : SearchPath :=
  System.FilePath.splitSearchPath path ++ sp

@[extern c inline "LEAN_IS_STAGE0"]
private constant isStage0 (u : Unit) : Bool

def getBuiltinSearchPath : IO SearchPath := do
  let appDir ← IO.appDir
  let mut buildDir := appDir / ".."
  -- use stage1 stdlib with stage0 executable (which should never be distributed outside of the build directory)
  if isStage0 () then
    buildDir := buildDir / ".." / "stage1"
  [buildDir / "lib" / "lean"]

def addSearchPathFromEnv (sp : SearchPath) : IO SearchPath := do
  let val ← IO.getEnv "LEAN_PATH"
  match val with
  | none     => pure sp
  | some val => parseSearchPath val sp

@[export lean_init_search_path]
def initSearchPath (path : Option String := none) : IO Unit :=
  match path with
  | some path => searchPathRef.set <| parseSearchPath path
  | none      => do
    let sp ← getBuiltinSearchPath
    let sp ← addSearchPathFromEnv sp
    searchPathRef.set sp

partial def findOLean (mod : Name) : IO FilePath := do
  let sp ← searchPathRef.get
  if let some fname ← sp.findWithExt ".olean" mod then
    return fname
  else
    let pkg : FilePath := mod.getRoot.toString
    let mut msg := s!"unknown package '{pkg}'"
    let rec maybeThisOne dir := do
      if ← (pkg / dir).isDir then
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
  let fname ← realPathNormalized fname
  let rootDir ← match rootDir with
    | some rootDir => pure rootDir
    | none         => IO.currentDir
  let mut rootDir ← realPathNormalized rootDir
  if !rootDir.endsWith System.FilePath.pathSeparator.toString then
    rootDir := rootDir ++ System.FilePath.pathSeparator.toString
  if !rootDir.isPrefixOf fname then
    throw $ IO.userError s!"input file '{fname}' must be contained in root directory ({rootDir})"
  let fnameSuffix := fname.drop rootDir.length
  let modNameStr := System.FilePath.withExtension fnameSuffix ""
  let modName    := modNameStr.components.foldl Name.mkStr Name.anonymous
  pure modName

end Lean
