/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Compile
import Lake.BuildTarget

open System
namespace Lake

-- # General Utilities

def buildFileUnlessUpToDate (file : FilePath)
(trace : BuildTrace) (build : BuildM PUnit) : BuildM BuildTrace := do
  let traceFile := FilePath.mk <| file.toString ++ ".trace"
  let (upToDate, trace) ← trace.check file traceFile
  unless upToDate do
    build
  IO.FS.writeFile traceFile trace.hash.toString
  liftM <| computeTrace file

def fileTargetWithDep (file : FilePath)
(depTarget : BuildTarget i) (build : i → BuildM PUnit) : FileTarget :=
  Target.mk file do
    depTarget.mapAsync fun depInfo depTrace => do
      buildFileUnlessUpToDate file depTrace <| build depInfo

def fileTargetWithDepList (file : FilePath)
(depTargets : List (BuildTarget i)) (build : List i → BuildM PUnit) : FileTarget :=
  Target.mk file do
    Target.collectList depTargets |>.mapAsync fun depInfos depTrace => do
      buildFileUnlessUpToDate file depTrace <| build depInfos

def fileTargetWithDepArray (file : FilePath)
(depTargets : Array (BuildTarget i)) (build : Array i → BuildM PUnit) : FileTarget :=
  Target.mk file do
    Target.collectArray depTargets |>.mapAsync fun depInfos depTrace => do
      buildFileUnlessUpToDate file depTrace <| build depInfos

-- # Specific Targets

def oFileTarget (oFile : FilePath) (srcTarget : FileTarget)
(args : Array String := #[]) (compiler : FilePath := "c++") : FileTarget :=
  fileTargetWithDep oFile srcTarget fun srcFile => do
    compileO oFile srcFile args compiler

def leanOFileTarget (oFile : FilePath)
(srcTarget : FileTarget) (args : Array String := #[]) : FileTarget :=
  fileTargetWithDep oFile srcTarget fun srcFile => do
    compileO oFile srcFile args (← getLeanc)

def staticLibTarget (libFile : FilePath)
(oFileTargets : Array FileTarget) (ar : FilePath := "ar") : FileTarget :=
  fileTargetWithDepArray libFile oFileTargets fun oFiles => do
    compileStaticLib libFile oFiles ar

def binTarget (binFile : FilePath) (linkTargets : Array FileTarget)
(linkArgs : Array String := #[]) (linker : FilePath := "cc") : FileTarget :=
   fileTargetWithDepArray binFile linkTargets fun links => do
    compileBin binFile links linkArgs linker

def leanBinTarget (binFile : FilePath) (linkTargets : Array FileTarget)
(linkArgs : Array String := #[]) (linker : FilePath := "cc") : FileTarget :=
  fileTargetWithDepArray binFile linkTargets fun links => do
    compileBin binFile links linkArgs (← getLeanc)
