/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich

Management of the Lean search path (`LEAN_PATH`), which is a list of
`pkg=path` mappings from package name to root path. An import `A.B.C`
given an `A=path` entry resolves to `path/B/C.olean`. A package-only
import `A` is normalized to `A.Default`. For the input file, we also
need the reverse direction of finding a (unique) module path from a
file path.
-/
prelude
import Init.System.IO
import Init.System.FilePath
import Init.Data.Array
import Init.Data.List.Control
import Init.Lean.Name
import Init.Data.HashMap
import Init.Data.Nat.Control

namespace Lean
open System.FilePath (pathSeparator extSeparator)
private def pathSep : String := toString pathSeparator

def realPathNormalized (fname : String) : IO String :=
do fname ← IO.realPath fname;
   pure (System.FilePath.normalizePath fname)

abbrev SearchPath := HashMap String String

def mkSearchPathRef : IO (IO.Ref SearchPath) :=
IO.mkRef ∅

@[init mkSearchPathRef]
constant searchPathRef : IO.Ref SearchPath := arbitrary _

def parseSearchPath (path : String) (sp : SearchPath := ∅) : IO SearchPath := do
  let ps := System.FilePath.splitSearchPath path;
  sp ← ps.foldlM (fun (sp : SearchPath) s => match s.splitOn "=" with
    | [pkg, path] => pure $ sp.insert pkg path
    | _           => throw $ IO.userError $ "ill-formed search path entry '" ++ s ++ "', should be of form 'pkg=path'")
    sp;
  pure sp

def getBuiltinSearchPath : IO SearchPath :=
do appDir ← IO.appDir;
   let libDir := appDir ++ pathSep ++ ".." ++ pathSep ++ "library" ++ pathSep ++ "Init";
   libDirExists ← IO.isDir libDir;
   if libDirExists then do
     path ← realPathNormalized libDir;
     pure $ HashMap.empty.insert "Init" path
   else do
     let installedLibDir := appDir ++ pathSep ++ ".." ++ pathSep ++ "lib" ++ pathSep ++ "lean" ++ pathSep ++ "library" ++ pathSep ++ "Init";
     installedLibDirExists ← IO.isDir installedLibDir;
     if installedLibDirExists then do
       path ← realPathNormalized installedLibDir;
       pure $ HashMap.empty.insert "Init" path
     else
       pure ∅

def addSearchPathFromEnv (sp : SearchPath) : IO SearchPath :=
do val ← IO.getEnv "LEAN_PATH";
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
| Name.str Name.anonymous h _ => h
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

@[export lean_find_olean]
def findOLean (mod : Name) : IO String :=
do sp ← searchPathRef.get;
   let (pkg, path) := splitAtRoot mod;
   some root ← pure $ sp.find pkg
     | throw $ IO.userError $ "unknown package '" ++ pkg ++ "'";
   let fname := root ++ pathSep ++ modPathToFilePath path ++ ".olean";
   pure fname

def findAtSearchPath (fname : String) : IO (Option (String × String)) :=
do fname ← realPathNormalized fname;
   sp ← searchPathRef.get;
   results ← sp.foldM (fun results pkg path => do
     path ← realPathNormalized path;
     pure $ if String.isPrefixOf path fname then (pkg, path) :: results else results) [];
   match results with
   | [res] => pure res
   | []    => pure none
   | _     => throw (IO.userError ("file '" ++ fname ++ "' is contained in multiple packages: " ++ ", ".intercalate (results.map Prod.fst)))

@[export lean_module_name_of_file]
def moduleNameOfFileName (fname : String) : IO (Option Name) :=
do some (pkg, path) ← findAtSearchPath fname
     | pure none;
   fname ← realPathNormalized fname;
   let fnameSuffix := fname.drop path.length;
   let fnameSuffix := if fnameSuffix.get 0 == pathSeparator then fnameSuffix.drop 1 else fnameSuffix;
   some extPos ← pure (fnameSuffix.revPosOf '.')
     | throw (IO.userError ("failed to convert file '" ++ fname ++ "' to module name, extension is missing"));
   let modNameStr := fnameSuffix.extract 0 extPos;
   let extStr     := fnameSuffix.extract (extPos + 1) fnameSuffix.bsize;
   let parts      := modNameStr.splitOn pathSep;
   let modName    := parts.foldl mkNameStr pkg;
   pure modName

/-- Absolutize and normalize parsed import. -/
@[export lean_module_name_of_rel_name]
def moduleNameOfRelName (baseMod : Option Name) (m : Name) (k : Option Nat) : IO Name := do
  m ← match k, baseMod with
  | none,   _            => pure m
  | some k, none         => throw (IO.userError ("invalid use of relative import, module name of main file is not available"))
  | some k, some baseMod => do {
    -- split out package name so that we cannot leave package
    let (pkg, path) := splitAtRoot baseMod;
    -- +1 to go from main file module to surrounding directory
    path ← (k + 1).foldM (fun _ path => match path with
      | Name.str path _ _ => pure path
      | Name.anonymous => throw $ IO.userError $ "invalid relative import, would leave package"
      | Name.num _ _ _ => unreachable!) path;
    pure $ pkg ++ path
  };
  -- normalize `A` to `A.Default`
  match m with
  | Name.str Name.anonymous pkg _ => pure $ mkNameSimple pkg ++ "Default"
  | _                             => pure m

end Lean
