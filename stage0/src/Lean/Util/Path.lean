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
open System.FilePath (pathSeparator extSeparator)
private def pathSep : String := toString pathSeparator

def realPathNormalized (fname : String) : IO String := do
  let fname ← IO.realPath fname
  pure (System.FilePath.normalizePath fname)

abbrev SearchPath := List String

builtin_initialize searchPathRef : IO.Ref SearchPath ← IO.mkRef {}

def parseSearchPath (path : String) (sp : SearchPath := ∅) : IO SearchPath :=
  pure $ System.FilePath.splitSearchPath path ++ sp

@[extern c inline "LEAN_IS_STAGE0"]
constant isStage0 (u : Unit) : Bool

def getBuiltinSearchPath : IO SearchPath := do
  let appDir ← IO.appDir
  -- use stage1 stdlib with stage0 executable (which should never be distributed outside of the build directory)
  pure [appDir ++ pathSep ++ ".." ++ (if isStage0 () then pathSep ++ ".." ++ pathSep ++ "stage1" else "") ++ pathSep ++ "lib" ++ pathSep ++ "lean"]

def addSearchPathFromEnv (sp : SearchPath) : IO SearchPath := do
  let val ← IO.getEnv "LEAN_PATH"
  match val with
  | none     => pure sp
  | some val => parseSearchPath val sp

@[export lean_init_search_path]
def initSearchPath (path : Option String := none) : IO Unit :=
  match path with
  | some path => parseSearchPath path >>= searchPathRef.set
  | none      => do
    let sp ← getBuiltinSearchPath
    let sp ← addSearchPathFromEnv sp
    searchPathRef.set sp

def modPathToFilePath : Name → String
  | Name.str p h _              => modPathToFilePath p ++ pathSep ++ h
  | Name.anonymous              => ""
  | Name.num p _ _              => panic! "ill-formed import"

def findOLean (mod : Name) : IO String := do
  let sp ← searchPathRef.get
  let pkg := mod.getRoot.toString
  let some root ← sp.findM? (fun path => IO.isDir $ path ++ pathSep ++ pkg)
    | throw $ IO.userError $ "unknown package '" ++ pkg ++ "'"
  pure $ root ++ modPathToFilePath mod ++ ".olean"

/-- Infer module name of source file name. -/
@[export lean_module_name_of_file]
def moduleNameOfFileName (fname : String) (rootDir : Option String) : IO Name := do
  let fname ← realPathNormalized fname
  let rootDir ← match rootDir with
    | some rootDir => pure rootDir
    | none         => IO.currentDir
  let rootDir ← realPathNormalized rootDir
  if !rootDir.isPrefixOf fname then
    throw $ IO.userError s!"input file '{fname}' must be contained in root directory ({rootDir})"
  let fnameSuffix := fname.drop rootDir.length
  let fnameSuffix := if fnameSuffix.get 0 == pathSeparator then fnameSuffix.drop 1 else fnameSuffix
  let some extPos ← pure (fnameSuffix.revPosOf '.')
    | throw (IO.userError ("failed to convert file name '" ++ fname ++ "' to module name, extension is missing"))
  let modNameStr := fnameSuffix.extract 0 extPos
  let extStr     := fnameSuffix.extract (extPos + 1) fnameSuffix.bsize
  let parts      := modNameStr.splitOn pathSep
  let modName    := parts.foldl mkNameStr Name.anonymous
  pure modName

end Lean
