/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.system.io
import init.system.filepath
import init.data.array

namespace Lean
open System.FilePath (pathSeparator searchPathSeparator)
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
   IO.println libDir;
   libDirExists ← IO.isDir libDir;
   if libDirExists then
     IO.realPath libDir
   else do
     let installedLibDir := appDir ++ pathSep ++ ".." ++ pathSep ++ "lib" ++ pathSep ++ "lean" ++ pathSep ++ "library";
     installedLibDirExists ← IO.isDir installedLibDir;
     IO.println installedLibDir;
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
     ex ← IO.fileExists curr;
     if ex then pure (some curr) else pure none

end Lean
