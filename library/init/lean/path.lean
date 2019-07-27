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

def mkSearchPathRef : IO (IO.Ref (Array String)) :=
do curr ← IO.realPath ".";
   IO.mkRef (Array.singleton curr)

@[init mkSearchPathRef]
constant searchPathRef : IO.Ref (Array String) := default _

def setSearchPath (s : List String) : IO Unit :=
do s ← s.mmap IO.realPath;
   searchPathRef.set s.toArray

def setSearchPathFromString (s : String) : IO Unit :=
setSearchPath (s.split searchPathSep)

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
| some path => setSearchPathFromString path
| none      => do
  path ← getSearchPathFromEnv;
  match path with
  | some path => setSearchPath path
  | none => do
    path ← getBuiltinSearchPath;
    curr ← IO.realPath ".";
    setSearchPath [path, curr]

def findFile (fname : String) : IO (Option (String × String)) :=
do paths ← searchPathRef.get;
   paths.mfind $ fun path => do
     let path := path ++ pathSep;
     let curr := path ++ fname;
     ex ← IO.fileExists curr;
     if ex then pure (some (path, curr)) else pure none

def modNameToFileName : Name → String
| (Name.mkString Name.anonymous h)  := h
| (Name.mkString p h)               := modNameToFileName p ++ pathSep ++ h
| Name.anonymous                    := ""
| (Name.mkNumeral p _)              := modNameToFileName p

def addRel (basePath : String) : Nat → String
| 0     := basePath
| (n+1) := addRel n ++ pathSep ++ ".."

def findLeanFile (rel : Option Nat) (modName : Name) (ext : String) : IO (String × String) :=
let fname := modNameToFileName modName ++ toString extSeparator ++ ext;
match rel with
| none => do
  some (path, fname) ← findFile fname | throw (IO.userError ("module '" ++ toString modName ++ "' not found"));
  fname ← IO.realPath fname;
  pure (path, fname)
| some n => do
  path  ← IO.realPath ".";
  let fname := addRel path n ++ pathSep ++ fname;
  ex ← IO.fileExists fname;
  unless ex $ throw (IO.userError ("module '" ++ toString modName ++ "' not found"));
  fname ← IO.realPath fname;
  pure (path, fname)

def findOLean (modName : Name) : IO String :=
Prod.snd <$> findLeanFile none modName "olean"

def findLean (rel : Option Nat) (modName : Name) : IO String :=
Prod.snd <$> findLeanFile rel modName "lean"

/-
def absolutizeModuleName (rel : Option Nat) (modName : Name) : IO Name :=
match rel with
| none => pure modName
| _    => do
  (path, fname) ← findOLean rel modName;
  let fname := fname.drop path.length;
  let fname := fname.take (fname.length - "olean".length - 1 /- path separator -/);
  let comps := fname.split pathSep;
  pure $ comps.foldl Name.mkString Name.anonymous
-/

end Lean
