/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Actions
import Lake.Build.TargetTypes

open System
namespace Lake

-- # General Utilities

def inputFileTarget (path : FilePath) : FileTarget :=
  Target.mk path <| async (m := BuildM) <| computeTrace path

instance : Coe FilePath FileTarget := ⟨inputFileTarget⟩

def buildUnlessUpToDate [CheckExists i] [GetMTime i] (info : i)
(depTrace : BuildTrace) (traceFile : FilePath) (build : BuildM PUnit) : BuildM PUnit := do
  let upToDate ← depTrace.checkAgainstFile info traceFile
  unless upToDate do
    build
    depTrace.writeToFile traceFile

def buildFileUnlessUpToDate (file : FilePath)
(depTrace : BuildTrace) (build : BuildM PUnit) : BuildM BuildTrace := do
  let traceFile := FilePath.mk <| file.toString ++ ".trace"
  buildUnlessUpToDate file depTrace traceFile build
  computeTrace file

def fileTargetWithDep (file : FilePath) (depTarget : BuildTarget i)
(build : i → BuildM PUnit) (extraDepTrace : BuildM _ := pure BuildTrace.nil) : FileTarget :=
  Target.mk file <| depTarget.bindSync fun depInfo depTrace => do
    buildFileUnlessUpToDate file (depTrace.mix (← extraDepTrace)) <| build depInfo

def fileTargetWithDepList (file : FilePath) (depTargets : List (BuildTarget i))
(build : List i → BuildM PUnit) (extraDepTrace : BuildM _ := pure BuildTrace.nil) : FileTarget :=
  fileTargetWithDep file (Target.collectList depTargets) build extraDepTrace

def fileTargetWithDepArray (file : FilePath) (depTargets : Array (BuildTarget i))
(build : Array i → BuildM PUnit) (extraDepTrace : BuildM _ := pure BuildTrace.nil) : FileTarget :=
  fileTargetWithDep file (Target.collectArray depTargets) build extraDepTrace

-- # Specific Targets

def oFileTarget (oFile : FilePath) (srcTarget : FileTarget)
(args : Array String := #[]) (compiler : FilePath := "c++") : FileTarget :=
  fileTargetWithDep oFile srcTarget (extraDepTrace := computeHash args) fun srcFile => do
    compileO oFile srcFile args compiler

def leanOFileTarget (oFile : FilePath)
(srcTarget : FileTarget) (args : Array String := #[]) : FileTarget :=
  fileTargetWithDep oFile srcTarget (extraDepTrace := computeHash args) fun srcFile => do
    compileO oFile srcFile args (← getLeanc)

def staticLibTarget (libFile : FilePath)
(oFileTargets : Array FileTarget) (ar : Option FilePath := none) : FileTarget :=
  fileTargetWithDepArray libFile oFileTargets fun oFiles => do
    compileStaticLib libFile oFiles (ar.getD (← getLeanAr))

def leanSharedLibTarget (binFile : FilePath)
(linkTargets : Array FileTarget) (linkArgs : Array String := #[]) : FileTarget :=
  fileTargetWithDepArray binFile linkTargets fun links => do
    compileSharedLib binFile links linkArgs (← getLeanc)

def cExeTarget (binFile : FilePath) (linkTargets : Array FileTarget)
(linkArgs : Array String := #[]) (linker : FilePath := "cc") : FileTarget :=
   fileTargetWithDepArray binFile linkTargets (extraDepTrace := computeHash linkArgs) fun links => do
    compileBin binFile links linkArgs linker

def leanExeTarget (binFile : FilePath)
(linkTargets : Array FileTarget) (linkArgs : Array String := #[]) : FileTarget :=
  fileTargetWithDepArray binFile linkTargets
  (extraDepTrace := getLeanTrace <&> (·.mix <| pureHash linkArgs)) fun links => do
    compileBin binFile links linkArgs (← getLeanc)
