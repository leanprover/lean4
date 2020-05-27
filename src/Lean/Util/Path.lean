/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

Management of the Lean search path (`LEAN_PATH`), which is a list of
paths containing package roots: an import `A.B.C` resolves to
`path/A/B/C.olean` for the first entry `path` in `LEAN_PATH`
with a directory `A/`. `import A` resolves to `path/A.olean`.
-/
prelude
import Init.System.IO
import Init.System.FilePath
import Init.Data.Array
import Init.Data.List.Control
import Init.Data.HashMap
import Init.Data.Nat.Control
import Lean.Data.Name

namespace Lean
open System.FilePath (pathSeparator extSeparator)
private def pathSep : String := toString pathSeparator

def realPathNormalized (fname : String) : IO String := do
fname ← IO.realPath fname;
pure (System.FilePath.normalizePath fname)

abbrev SearchPath := List String

def mkSearchPathRef : IO (IO.Ref SearchPath) :=
IO.mkRef ∅

@[init mkSearchPathRef]
constant searchPathRef : IO.Ref SearchPath := arbitrary _

def parseSearchPath (path : String) (sp : SearchPath := ∅) : IO SearchPath :=
pure $ System.FilePath.splitSearchPath path ++ sp

def getBuiltinSearchPath : IO SearchPath := do
appDir ← IO.appDir;
pure [appDir ++ pathSep ++ ".." ++ pathSep ++ "lib" ++ pathSep ++ "lean"]

def addSearchPathFromEnv (sp : SearchPath) : IO SearchPath := do
val ← IO.getEnv "LEAN_PATH";
match val with
| none     => pure sp
| some val => parseSearchPath val sp

@[export lean_init_search_path]
def initSearchPath (path : Option String := none) : IO Unit :=
match path with
| some path => parseSearchPath path >>= searchPathRef.set
| none      => do
  sp ← getBuiltinSearchPath;
  sp ← addSearchPathFromEnv sp;
  searchPathRef.set sp

def modPathToFilePath : Name → String
| Name.str p h _              => modPathToFilePath p ++ pathSep ++ h
| Name.anonymous              => ""
| Name.num p _ _              => panic! "ill-formed import"

def findOLean (mod : Name) : IO String := do
sp ← searchPathRef.get;
let pkg := mod.getRoot.toString;
some root ← sp.findM? (fun path => IO.isDir $ path ++ pathSep ++ pkg)
  | throw $ IO.userError $ "unknown package '" ++ pkg ++ "'";
pure $ root ++ modPathToFilePath mod ++ ".olean"

/-- Infer module name of source file name, assuming that `lean` is called from the package source root. -/
@[export lean_module_name_of_file]
def moduleNameOfFileName (fname : String) : IO Name := do
fname ← realPathNormalized fname;
root ← IO.currentDir >>= realPathNormalized;
when (!root.isPrefixOf fname) $
  throw $ IO.userError $ "input file '" ++ fname ++ "' must be contained in current directory (" ++ root ++ ")";
let fnameSuffix := fname.drop root.length;
let fnameSuffix := if fnameSuffix.get 0 == pathSeparator then fnameSuffix.drop 1 else fnameSuffix;
some extPos ← pure (fnameSuffix.revPosOf '.')
  | throw (IO.userError ("failed to convert file name '" ++ fname ++ "' to module name, extension is missing"));
let modNameStr := fnameSuffix.extract 0 extPos;
let extStr     := fnameSuffix.extract (extPos + 1) fnameSuffix.bsize;
let parts      := modNameStr.splitOn pathSep;
let modName    := parts.foldl mkNameStr Name.anonymous;
pure modName

end Lean
