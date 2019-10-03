/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.system.io
import init.system.filepath
import init.data.array
import init.control.combinators
import init.lean.name

namespace Lean
open System.FilePath (pathSeparator searchPathSeparator extSeparator)
private def pathSep : String := toString pathSeparator
private def searchPathSep : String := toString searchPathSeparator

def realPathNormalized (fname : String) : IO String :=
do fname ← IO.realPath fname;
   pure (System.FilePath.normalizePath fname)

def mkSearchPathRef : IO (IO.Ref (Array String)) :=
do curr ← realPathNormalized ".";
   IO.mkRef (Array.singleton curr)

@[init mkSearchPathRef]
constant searchPathRef : IO.Ref (Array String) := default _

def setSearchPath (s : List String) : IO Unit :=
do s ← s.mmap realPathNormalized;
   searchPathRef.set s.toArray

def setSearchPathFromString (s : String) : IO Unit :=
setSearchPath (s.split searchPathSep)

def getBuiltinSearchPath : IO (List String) :=
do appDir ← IO.appDir;
   let libDir := appDir ++ pathSep ++ ".." ++ pathSep ++ "library";
   libDirExists ← IO.isDir libDir;
   if libDirExists then do
     path ← realPathNormalized libDir;
     pure [path]
   else do
     let installedLibDir := appDir ++ pathSep ++ ".." ++ pathSep ++ "lib" ++ pathSep ++ "lean" ++ pathSep ++ "library";
     installedLibDirExists ← IO.isDir installedLibDir;
     if installedLibDirExists then do
       path ← realPathNormalized installedLibDir;
       pure [path]
     else
       pure []

def getSearchPathFromEnv : IO (List String) :=
do val ← IO.getEnv "LEAN_PATH";
   match val with
   | none     => pure ["."] -- If LEAN_PATH is not defined, use current directory
   | some val => pure (val.split searchPathSep)

@[export lean_init_search_path]
def initSearchPath (path : Option String := "") : IO Unit :=
match path with
| some path => setSearchPathFromString path
| none      => do
  pathEnv     ← getSearchPathFromEnv;
  builtinPath ← getBuiltinSearchPath;
  setSearchPath (pathEnv ++ builtinPath)

def findFile (fname : String) (ext : String) : IO (Option String) :=
let checkFile (curr : String) : IO (Option String) := do {
  ex ← IO.fileExists curr;
  if ex then pure (some curr) else pure none
};
do let fname := System.FilePath.normalizePath fname;
   paths ← searchPathRef.get;
   paths.mfind $ fun path => do
     let curr := path ++ pathSep ++ fname;
     result ← checkFile (curr ++ toString extSeparator ++ ext);
     match result with
     | none  => checkFile (curr ++ pathSep ++ "default" ++ toString extSeparator ++ ext)
     | other => pure other

def modNameToFileName : Name → String
| Name.mkString Name.anonymous h => h
| Name.mkString p h              => modNameToFileName p ++ pathSep ++ h
| Name.anonymous                 => ""
| Name.mkNumeral p _             => modNameToFileName p

def addRel (baseDir : String) : Nat → String
| 0   => baseDir
| n+1 => addRel n ++ pathSep ++ ".."

def findLeanFile (modName : Name) (ext : String) : IO String :=
do
let fname := modNameToFileName modName;
some fname ← findFile fname ext | throw (IO.userError ("module '" ++ toString modName ++ "' not found"));
realPathNormalized fname

def findOLean (modName : Name) : IO String :=
findLeanFile modName "olean"

@[export lean_find_lean]
def findLean (modName : Name) : IO String :=
findLeanFile modName "lean"

def findAtSearchPath (fname : String) : IO String :=
do fname ← realPathNormalized fname;
   paths ← searchPathRef.get;
   match paths.find? (fun path => if path.isPrefixOf fname then some path else none) with
   | some r => pure r
   | none   => throw (IO.userError ("file '" ++ fname ++ "' not in the search path " ++ repr paths))

@[export lean_module_name_of_file]
def moduleNameOfFileName (fname : String) : IO Name :=
do
path  ← findAtSearchPath fname;
fname ← realPathNormalized fname;
let fnameSuffix := fname.drop path.length;
let fnameSuffix := if fnameSuffix.get 0 == pathSeparator then fnameSuffix.drop 1 else fnameSuffix;
if path ++ pathSep ++ fnameSuffix != fname then
  throw (IO.userError ("failed to convert file '" ++ fname ++ "' to module name, path is not a prefix of the given file"))
else do
  some extPos ← pure (fnameSuffix.revPosOf '.')
    | throw (IO.userError ("failed to convert file '" ++ fname ++ "' to module name, extension is missing"));
  let modNameStr := fnameSuffix.extract 0 extPos;
  let extStr     := fnameSuffix.extract (extPos + 1) fnameSuffix.bsize;
  let parts      := modNameStr.split pathSep;
  let modName    := parts.foldl Name.mkString Name.anonymous;
  fname' ← findLeanFile modName extStr;
  unless (fname == fname') $ throw (IO.userError ("failed to convert file '" ++ fname ++ "' to module name, module name '" ++ toString modName ++ "' resolves to '" ++ fname' ++ "'"));
  pure modName

end Lean
