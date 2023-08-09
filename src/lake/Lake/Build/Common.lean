/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Monad
import Lake.Build.Actions

open System
namespace Lake

/-! # General Utilities -/

@[inline] def inputFile (path : FilePath) : SchedulerM (BuildJob FilePath) :=
  Job.async <| (path, ·) <$> computeTrace path

@[inline] def buildUnlessUpToDate [CheckExists ι] [GetMTime ι] (info : ι)
(depTrace : BuildTrace) (traceFile : FilePath) (build : JobM PUnit) : JobM PUnit := do
  let isOldMode ← getIsOldMode
  let upToDate ←
    if isOldMode then
      depTrace.checkAgainstTime info
    else
      depTrace.checkAgainstFile info traceFile
  unless upToDate do
    build
    unless isOldMode do
      depTrace.writeToFile traceFile

@[inline] def buildFileUnlessUpToDate (file : FilePath)
(depTrace : BuildTrace) (build : BuildM PUnit) : BuildM BuildTrace := do
  let traceFile := FilePath.mk <| file.toString ++ ".trace"
  buildUnlessUpToDate file depTrace traceFile build
  computeTrace file

@[inline] def buildFileAfterDep
(file : FilePath) (dep : BuildJob α) (build : α → BuildM PUnit)
(extraDepTrace : BuildM _ := pure BuildTrace.nil) : SchedulerM (BuildJob FilePath) :=
  dep.bindSync fun depInfo depTrace => do
    let depTrace := depTrace.mix (← extraDepTrace)
    let trace ← buildFileUnlessUpToDate file depTrace <| build depInfo
    return (file, trace)

@[inline] def buildFileAfterDepList
(file : FilePath) (deps : List (BuildJob α)) (build : List α → BuildM PUnit)
(extraDepTrace : BuildM _ := pure BuildTrace.nil) : SchedulerM (BuildJob FilePath) := do
  buildFileAfterDep file (← BuildJob.collectList deps) build extraDepTrace

@[inline] def buildFileAfterDepArray
(file : FilePath) (deps : Array (BuildJob α)) (build : Array α → BuildM PUnit)
(extraDepTrace : BuildM _ := pure BuildTrace.nil) : SchedulerM (BuildJob FilePath) := do
  buildFileAfterDep file (← BuildJob.collectArray deps) build extraDepTrace

/-! # Common Builds -/

def buildO (name : String)
(oFile : FilePath) (srcJob : BuildJob FilePath)
(args : Array String := #[]) (compiler : FilePath := "cc") : SchedulerM (BuildJob FilePath) :=
  buildFileAfterDep oFile srcJob (extraDepTrace := computeHash args) fun srcFile => do
     compileO name oFile srcFile args compiler

def buildLeanO (name : String)
(oFile : FilePath) (srcJob : BuildJob FilePath)
(args : Array String := #[]) : SchedulerM (BuildJob FilePath) :=
  buildFileAfterDep oFile srcJob (extraDepTrace := computeHash args) fun srcFile => do
     compileO name oFile srcFile args (← getLeanc)

def buildStaticLib (libFile : FilePath)
(oFileJobs : Array (BuildJob FilePath)) : SchedulerM (BuildJob FilePath) :=
  let name := libFile.fileName.getD libFile.toString
  buildFileAfterDepArray libFile oFileJobs fun oFiles => do
    compileStaticLib name libFile oFiles (← getLeanAr)

def buildLeanSharedLib
(libFile : FilePath) (linkJobs : Array (BuildJob FilePath))
(linkArgs : Array String := #[]) : SchedulerM (BuildJob FilePath) :=
  let name := libFile.fileName.getD libFile.toString
  buildFileAfterDepArray libFile linkJobs
  (extraDepTrace := computeHash linkArgs) fun links => do
    compileSharedLib name libFile (links.map toString ++ linkArgs) (← getLeanc)

def buildLeanExe
(exeFile : FilePath) (linkJobs : Array (BuildJob FilePath))
(linkArgs : Array String := #[]) : SchedulerM (BuildJob FilePath) :=
  let name := exeFile.fileName.getD exeFile.toString
  buildFileAfterDepArray exeFile linkJobs
  (extraDepTrace := computeHash linkArgs) fun links => do
    compileExe name exeFile links linkArgs (← getLeanc)

def buildLeanSharedLibOfStatic (staticLibJob : BuildJob FilePath)
(linkArgs : Array String := #[]) : SchedulerM (BuildJob FilePath) :=
  staticLibJob.bindSync fun staticLib staticTrace => do
    let dynlib := staticLib.withExtension sharedLibExt
    let baseArgs :=
      if System.Platform.isOSX then
        #[s!"-Wl,-force_load,{staticLib}"]
      else
        #["-Wl,--whole-archive", staticLib.toString, "-Wl,--no-whole-archive"]
    let args := baseArgs ++ linkArgs
    let depTrace := staticTrace.mix (← computeHash args)
    let trace ← buildFileUnlessUpToDate dynlib depTrace do
      let name := dynlib.fileName.getD dynlib.toString
      compileSharedLib name dynlib args (← getLeanc)
    return (dynlib, trace)

def computeDynlibOfShared
(sharedLibTarget : BuildJob FilePath) : SchedulerM (BuildJob Dynlib) :=
  sharedLibTarget.bindSync fun sharedLib trace => do
    if let some stem := sharedLib.fileStem then
      if Platform.isWindows then
        return ({path := sharedLib, name := stem}, trace)
      else if stem.startsWith "lib" then
        return ({path := sharedLib, name := stem.drop 3}, trace)
      else
        error s!"shared library `{sharedLib}` does not start with `lib`; this is not supported on Unix"
    else
      error s!"shared library `{sharedLib}` has no file name"
