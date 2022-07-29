/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Actions
import Lake.Build.TargetTypes
import Lake.Build.Monad

open System
namespace Lake

/-! # General Utilities -/

def inputFileTarget (path : FilePath) : FileTarget :=
  Target.mk <| async (m := BuildM) <| (path, ·) <$> computeTrace path

instance : Coe FilePath FileTarget := ⟨inputFileTarget⟩

def buildUnlessUpToDate [CheckExists ι] [GetMTime ι] (info : ι)
(depTrace : BuildTrace) (traceFile : FilePath) (build : JobM PUnit) : JobM PUnit := do
  let upToDate ← depTrace.checkAgainstFile info traceFile
  unless upToDate do
    build
    depTrace.writeToFile traceFile

def buildFileUnlessUpToDate (file : FilePath)
(depTrace : BuildTrace) (build : BuildM PUnit) : BuildM BuildTrace := do
  let traceFile := FilePath.mk <| file.toString ++ ".trace"
  buildUnlessUpToDate file depTrace traceFile build
  computeTrace file

def fileTargetWithDep (file : FilePath) (depTarget : BuildTarget ι)
(build : ι → BuildM PUnit) (extraDepTrace : BuildM _ := pure BuildTrace.nil) : FileTarget :=
  Target.mk <| depTarget.bindSync fun depInfo depTrace => do
    let depTrace := depTrace.mix (← extraDepTrace)
    let trace ← buildFileUnlessUpToDate file depTrace <| build depInfo
    return (file, trace)

def fileTargetWithDepList (file : FilePath) (depTargets : List (BuildTarget ι))
(build : List ι → BuildM PUnit) (extraDepTrace : BuildM _ := pure BuildTrace.nil) : FileTarget :=
  fileTargetWithDep file (Target.collectList depTargets) build extraDepTrace

def fileTargetWithDepArray (file : FilePath) (depTargets : Array (BuildTarget ι))
(build : Array ι → BuildM PUnit) (extraDepTrace : BuildM _ := pure BuildTrace.nil) : FileTarget :=
  fileTargetWithDep file (Target.collectArray depTargets) build extraDepTrace

/-! # Specific Targets -/

def oFileTarget (name : String) (oFile : FilePath) (srcTarget : FileTarget)
(args : Array String := #[]) (compiler : FilePath := "c++") : FileTarget :=
  fileTargetWithDep oFile srcTarget (extraDepTrace := computeHash args) fun srcFile => do
    compileO name oFile srcFile args compiler

def leanOFileTarget (name : String) (oFile : FilePath)
(srcTarget : FileTarget) (args : Array String := #[]) : FileTarget :=
  fileTargetWithDep oFile srcTarget (extraDepTrace := computeHash args) fun srcFile => do
    compileO name oFile srcFile args (← getLeanc)

def staticLibTarget (name : String) (libFile : FilePath)
(oFileTargets : Array FileTarget) (ar : Option FilePath := none) : FileTarget :=
  fileTargetWithDepArray libFile oFileTargets fun oFiles => do
    compileStaticLib name libFile oFiles (ar.getD (← getLeanAr))

def cSharedLibTarget (name : String) (libFile : FilePath)
(linkTargets : Array FileTarget) (linkArgs : Array String := #[])
(linker : FilePath := "cc"): FileTarget :=
  fileTargetWithDepArray libFile linkTargets fun links => do
    compileSharedLib name libFile (links.map toString ++ linkArgs) linker

def leanSharedLibTarget (name : String) (libFile : FilePath)
(linkTargets : Array FileTarget) (linkArgs : Array String := #[]) : FileTarget :=
  fileTargetWithDepArray libFile linkTargets fun links => do
    compileSharedLib name libFile (links.map toString ++ linkArgs) (← getLeanc)

def cExeTarget (name : String) (exeFile : FilePath) (linkTargets : Array FileTarget)
(linkArgs : Array String := #[]) (linker : FilePath := "cc") : FileTarget :=
  fileTargetWithDepArray exeFile linkTargets (extraDepTrace := computeHash linkArgs) fun links => do
    compileExe name exeFile links linkArgs linker

def leanExeTarget (name : String) (exeFile : FilePath)
(linkTargets : Array FileTarget) (linkArgs : Array String := #[]) : FileTarget :=
  fileTargetWithDepArray exeFile linkTargets
  (extraDepTrace := getLeanTrace <&> (·.mix <| pureHash linkArgs)) fun links => do
    compileExe name exeFile links linkArgs (← getLeanc)

def staticToLeanSharedLibTarget (name : String) (staticLibTarget : FileTarget) : FileTarget :=
  .mk <| staticLibTarget.bindSync fun staticLib staticTrace => do
    let dynlib := staticLib.withExtension sharedLibExt
    let trace ← buildFileUnlessUpToDate dynlib staticTrace do
      let args :=
        if System.Platform.isOSX then
          #[s!"-Wl,-force_load,{staticLib}"]
        else
          #["-Wl,--whole-archive", staticLib.toString, "-Wl,--no-whole-archive"]
      compileSharedLib name dynlib args (← getLeanc)
    return (dynlib, trace)

def sharedToLeanDynlibTarget (sharedLibTarget : FileTarget) : DynlibTarget :=
  .mk <| sharedLibTarget.bindSync fun sharedLib trace => do
    if let some stem := sharedLib.fileStem then
      if Platform.isWindows then
        return ((sharedLib.parent, stem), trace)
      else if stem.startsWith "lib" then
        return ((sharedLib.parent, stem.drop 3), trace)
      else
        error s!"shared library `{sharedLib}` does not start with `lib`; this is not supported on Unix"
    else
      error s!"shared library `{sharedLib}` has no file name"
