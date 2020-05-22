/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

Management of the Lean search path (`LEAN_PATH`), which is a list of
`pkg=path` mappings from package name to root path. An import `A.B.C`
given an `A=path` entry resolves to `path/B/C.olean`, and just `A` to
`path.olean` (meaning that `path` should probably end with `/A`).
-/
prelude
import Init.System.IO
import Init.System.FilePath
import Init.Data.Array
import Init.Data.List.Control
import Init.Data.HashMap
import Init.Data.Nat.Control
import Init.Lean.Data.Name

namespace Lean
open System.FilePath (pathSeparator extSeparator)
private def pathSep : String := toString pathSeparator

def realPathNormalized (fname : String) : IO String := do
fname ← IO.realPath fname;
pure (System.FilePath.normalizePath fname)

abbrev SearchPath := HashMap String String

def mkSearchPathRef : IO (IO.Ref SearchPath) :=
IO.mkRef ∅

@[init mkSearchPathRef]
constant searchPathRef : IO.Ref SearchPath := arbitrary _

def parseSearchPath (path : String) (sp : SearchPath := ∅) : IO SearchPath := do
let ps := System.FilePath.splitSearchPath path;
sp ← ps.foldlM (fun (sp : SearchPath) s => match s.splitOn "=" with
  | [pkg, path] => do
    condM (IO.isDir path)
      (pure $ sp.insert pkg path)
      (throw $ IO.userError $ "invalid search path, '" ++ path ++ "' is not a directory")
  | _           => throw $ IO.userError $ "ill-formed search path entry '" ++ s ++ "', should be of form 'pkg=path'")
  sp;
pure sp

def getBuiltinSearchPath : IO SearchPath := do
appDir ← IO.appDir;
let installedLibDir := appDir ++ pathSep ++ ".." ++ pathSep ++ "lib" ++ pathSep ++ "lean" ++ pathSep ++ "Init";
installedLibDirExists ← IO.isDir installedLibDir;
if installedLibDirExists then do
  initPath ← realPathNormalized installedLibDir;
  let map := HashMap.empty.insert "Init" initPath;
  let stdDir := appDir ++ pathSep ++ ".." ++ pathSep ++ "lib" ++ pathSep ++ "lean" ++ pathSep ++ "Std";
  stdPath ← realPathNormalized stdDir;
  pure $ map.insert "Std" stdPath
else
  pure ∅

def addSearchPathFromEnv (sp : SearchPath) : IO SearchPath := do
val ← IO.getEnv "LEAN_PATH";
match val with
| none     => pure sp
| some val => parseSearchPath val sp

@[export lean_init_search_path]
def initSearchPath (path : Option String := "") : IO Unit :=
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

/- Given `A.B.C, return ("A", `B.C). -/
def splitAtRoot : Name → String × Name
| Name.str Name.anonymous s _ => (s, Name.anonymous)
| Name.str n s _ =>
  let (pkg, path) := splitAtRoot n;
  (pkg, mkNameStr path s)
| _              => panic! "ill-formed import"

def findOLean (mod : Name) : IO String := do
sp ← searchPathRef.get;
let (pkg, path) := splitAtRoot mod;
some root ← pure $ sp.find? pkg
  | throw $ IO.userError $ "unknown package '" ++ pkg ++ "'";
let fname := root ++ modPathToFilePath path ++ ".olean";
pure fname

def findAtSearchPath (fname : String) : IO (Option (String × String)) := do
fname ← realPathNormalized fname;
sp ← searchPathRef.get;
results ← sp.foldM (fun results pkg path => do
  path ← realPathNormalized path;
  pure $ if String.isPrefixOf path fname then (pkg, path) :: results else results) [];
match results with
| [res] => pure res
| []    => pure none
   | _     => throw (IO.userError ("file '" ++ fname ++ "' is contained in multiple packages: " ++ ", ".intercalate (results.map Prod.fst)))

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
