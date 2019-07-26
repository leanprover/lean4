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
import init.lean.modulename

namespace Lean
open System.FilePath (pathSeparator searchPathSeparator extSeparator)
private def pathSep : String := toString pathSeparator
private def searchPathSep : String := toString searchPathSeparator

def mkSearchPathRef : IO (IO.Ref (Array String)) :=
do curr ← IO.realPath ".";
   IO.mkRef (Array.singleton curr)

@[init mkSearchPathRef]
constant searchPathRef : IO.Ref (Array String) := default _

def setSearchPath (s : String) : IO Unit :=
searchPathRef.set (s.split searchPathSep).toArray

def getBuiltinSearchPath : IO String :=
do appDir ← IO.appDir;
   let libDir := appDir ++ pathSep ++ ".." ++ pathSep ++ "library";
   libDirExists ← IO.isDir libDir;
   if libDirExists then
     IO.realPath libDir
   else do
     let installedLibDir := appDir ++ pathSep ++ ".." ++ pathSep ++ "lib" ++ pathSep ++ "lean" ++ pathSep ++ "library";
     installedLibDirExists ← IO.isDir installedLibDir;
     if installedLibDirExists then do
       IO.realPath installedLibDir
     else
       throw (IO.userError "failed to locate builtin search path, please set LEAN_PATH")

def getSearchPathFromEnv : IO (Option (List String)) :=
do val ← IO.getEnv "LEAN_PATH";
   match val with
   | none     => pure none
   | some val =>
     pure $ val.split searchPathSep

@[export lean.init_search_path_core]
def initSearchPath (path : Option String := "") : IO Unit :=
match path with
| some path => setSearchPath path
| none      => do
  path ← getSearchPathFromEnv;
  match path with
  | some path => searchPathRef.set path.toArray
  | none => do
    path ← getBuiltinSearchPath;
    curr ← IO.realPath ".";
    searchPathRef.set [path, curr].toArray

def findFile (fname : String) : IO (Option String) :=
do paths ← searchPathRef.get;
   paths.mfind $ fun path => do
     let curr := path ++ pathSep ++ fname;
     IO.println ("trying " ++ curr);
     ex ← IO.fileExists curr;
     if ex then pure (some curr) else pure none

def modNameToFileName : Name → String
| (Name.mkString Name.anonymous h)  := h
| (Name.mkString p h)               := modNameToFileName p ++ pathSep ++ h
| Name.anonymous                    := ""
| (Name.mkNumeral p _)              := modNameToFileName p

def addRel : Nat → String
| 0     := "."
| (n+1) := addRel n ++ pathSep ++ ".."

def findLeanFile (modName : ModuleName) (ext : String) : IO String :=
match modName with
| ModuleName.explicit modName => do
  let fname := modNameToFileName modName ++ toString extSeparator ++ ext;
  some fname ← findFile fname | throw (IO.userError ("module '" ++ toString modName ++ "' not found"));
  IO.realPath fname
| ModuleName.relative n modName => do
  let fname := modNameToFileName modName ++ toString extSeparator ++ ext;
  let fname := addRel n ++ pathSep ++ fname;
  ex ← IO.fileExists fname;
  unless ex $ throw (IO.userError ("module '" ++ toString modName ++ "' not found"));
  IO.realPath fname

def findOLean (modName : ModuleName) : IO String :=
findLeanFile modName "olean"

def findLean (modName : Name) : IO String :=
findLeanFile modName "lean"

end Lean
