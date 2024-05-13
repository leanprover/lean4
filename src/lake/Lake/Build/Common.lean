/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Config.Monad
import Lake.Build.Actions

/-! # Common Build Tools
This file defines general utilities that abstract common
build functionality and provides some common concrete build functions.
-/

open System Lean

namespace Lake

/-! ## General Utilities -/

/--
Build trace for the host platform.
If an artifact includes this in its trace, it is platform-dependent
and will be rebuilt on different host platforms.
-/
def platformTrace := pureHash System.Platform.target

/-- Check if the `info` is up-to-date by comparing `depTrace` with `traceFile`. -/
@[specialize] def BuildTrace.checkUpToDate
  [CheckExists ι] [GetMTime ι]
  (info : ι) (depTrace : BuildTrace) (traceFile : FilePath)
: JobM Bool := do
  if (← getIsOldMode) then
    depTrace.checkAgainstTime info
  else
    depTrace.checkAgainstFile info traceFile

/--
Build `info` unless it already exists and `depTrace` matches that
of the `traceFile`. If rebuilt, save the new `depTrace` to the `tracefile`.
Returns whether `info` was already up-to-date.
-/
@[inline] def buildUnlessUpToDate?
  [CheckExists ι] [GetMTime ι] (info : ι)
  (depTrace : BuildTrace) (traceFile : FilePath) (build : JobM PUnit)
: JobM Bool := do
  if (← depTrace.checkUpToDate info traceFile) then
    return true
  else if (← getNoBuild) then
    IO.Process.exit noBuildCode.toUInt8
  else
    build
    depTrace.writeToFile traceFile
    return false

/--
Build `info` unless it already exists and `depTrace` matches that
of the `traceFile`. If rebuilt, save the new `depTrace` to the `tracefile`.
-/
@[inline] def buildUnlessUpToDate
  [CheckExists ι] [GetMTime ι] (info : ι)
  (depTrace : BuildTrace) (traceFile : FilePath) (build : JobM PUnit)
: JobM PUnit := do
  discard <| buildUnlessUpToDate? info depTrace traceFile build

/-- Fetch the trace of a file that may have its hash already cached in a `.hash` file. -/
def fetchFileTrace (file : FilePath) : JobM BuildTrace := do
  if (← getTrustHash) then
    let hashFile := FilePath.mk <| file.toString ++ ".hash"
    if let some hash ← Hash.load? hashFile then
      return .mk hash (← getMTime file)
    else
      let hash ← computeHash file
      IO.FS.writeFile hashFile hash.toString
      return .mk hash (← getMTime file)
  else
    computeTrace file

/-- Compute the hash of a file and save it to a `.hash` file. -/
def cacheFileHash (file : FilePath) : IO Hash := do
  let hash ← computeHash file
  let hashFile := FilePath.mk <| file.toString ++ ".hash"
  IO.FS.writeFile hashFile hash.toString
  return hash

/--
Replays the JSON log in `logFile` (if it exists).
If the log file is malformed, logs a warning.
-/
def replayBuildLog (logFile : FilePath) : LogIO PUnit := do
  match (← IO.FS.readFile logFile |>.toBaseIO) with
  | .ok contents =>
    match Json.parse contents >>= fromJson? with
    | .ok entries => Log.mk entries |>.replay
    | .error e => logWarning s!"cached build log is corrupted: {e}"
  | .error (.noFileOrDirectory ..) => pure ()
  | .error e => logWarning s!"failed to read cached build log: {e}"

/-- Saves the log produce by `build` as JSON to `logFile`. -/
def cacheBuildLog (logFile : FilePath) (build : JobM PUnit) : JobM PUnit := do
  let iniPos ← getLogPos
  let errPos? ← try build; pure none catch errPos => pure (some errPos)
  let log := (← getLog).takeFrom iniPos
  unless log.isEmpty do
    IO.FS.writeFile logFile (toJson log).pretty
  if let some errPos := errPos? then throw errPos

/--
Builds `file` using `build` unless it already exists and `depTrace` matches
the trace stored in the `.trace` file. If built, save the new `depTrace` and
cache `file`'s hash in a `.hash` file. Otherwise, try to fetch the hash from
the `.hash` file using `fetchFileTrace`. Build logs (if any) are saved to
a `.log.json` file and replayed from there if the build is skipped.

For example, given `file := "foo.c"`, compares `depTrace` with that in
`foo.c.trace` with the hash cache in `foo.c.hash` and the log cache in
`foo.c.log.json`.
-/
def buildFileUnlessUpToDate
  (file : FilePath) (depTrace : BuildTrace) (build : JobM PUnit)
: JobM BuildTrace := do
  let traceFile := FilePath.mk <| file.toString ++ ".trace"
  let logFile := FilePath.mk <| file.toString ++ ".log.json"
  let build := cacheBuildLog logFile build
  if (← buildUnlessUpToDate? file depTrace traceFile build) then
    replayBuildLog logFile
    fetchFileTrace file
  else
    return .mk (← cacheFileHash file) (← getMTime file)

/--
Build `file` using `build` after `dep` completes if the dependency's
trace (and/or `extraDepTrace`) has changed.
-/
@[inline] def buildFileAfterDep
  (file : FilePath) (dep : BuildJob α) (build : α → JobM PUnit)
  (extraDepTrace : JobM _ := pure BuildTrace.nil)
: SpawnM (BuildJob FilePath) :=
  dep.bindSync fun depInfo depTrace => do
    let depTrace := depTrace.mix (← extraDepTrace)
    let trace ← buildFileUnlessUpToDate file depTrace <| build depInfo
    return (file, trace)

/-- Build `file` using `build` after `deps` have built if any of their traces change. -/
@[inline] def buildFileAfterDepList
  (file : FilePath) (deps : List (BuildJob α)) (build : List α → JobM PUnit)
  (extraDepTrace : JobM _ := pure BuildTrace.nil)
: SpawnM (BuildJob FilePath) := do
  buildFileAfterDep file (← BuildJob.collectList deps) build extraDepTrace

/-- Build `file` using `build` after `deps` have built if any of their traces change. -/
@[inline] def buildFileAfterDepArray
  (file : FilePath) (deps : Array (BuildJob α)) (build : Array α → JobM PUnit)
  (extraDepTrace : JobM _ := pure BuildTrace.nil)
: SpawnM (BuildJob FilePath) := do
  buildFileAfterDep file (← BuildJob.collectArray deps) build extraDepTrace

/-! ## Common Builds -/

/-- A build job for file that is expected to already exist (e.g., a source file). -/
def inputFile (path : FilePath) : SpawnM (BuildJob FilePath) :=
  Job.async <| (path, ·) <$> computeTrace path

/--
Build an object file from a source file job using `compiler`. The invocation is:

```
compiler -c -o oFile srcFile weakArgs... traceArgs...
```

The `traceArgs` are included as part of the dependency trace hash, whereas
the `weakArgs` are not. Thus, system-dependent options like `-I` or `-L` should
be `weakArgs` to avoid build artifact incompatibility between systems
(i.e., a change in the file path should not cause a rebuild).

You can add more components to the trace via `extraDepTrace`,
which will be computed in the resulting `BuildJob` before building.
-/
@[inline] def buildO
  (oFile : FilePath) (srcJob : BuildJob FilePath)
  (weakArgs traceArgs : Array String := #[]) (compiler : FilePath := "cc")
  (extraDepTrace : JobM _ := pure BuildTrace.nil)
: SpawnM (BuildJob FilePath) :=
  let extraDepTrace :=
    return (← extraDepTrace).mix <| (pureHash traceArgs).mix platformTrace
  buildFileAfterDep oFile srcJob (extraDepTrace := extraDepTrace) fun srcFile => do
    compileO oFile srcFile (weakArgs ++ traceArgs) compiler

/-- Build an object file from a source fie job (i.e, a `lean -c` output) using `leanc`. -/
@[inline] def buildLeanO
  (oFile : FilePath) (srcJob : BuildJob FilePath)
  (weakArgs traceArgs : Array String := #[])
: SpawnM (BuildJob FilePath) :=
  let extraDepTrace :=
    return (← getLeanTrace).mix <| (pureHash traceArgs).mix platformTrace
  buildFileAfterDep oFile srcJob (extraDepTrace := extraDepTrace) fun srcFile => do
     compileO oFile srcFile (weakArgs ++ traceArgs) (← getLeanc)

/-- Build a static library from object file jobs using the `ar` packaged with Lean. -/
def buildStaticLib
  (libFile : FilePath) (oFileJobs : Array (BuildJob FilePath))
: SpawnM (BuildJob FilePath) :=
  buildFileAfterDepArray libFile oFileJobs fun oFiles => do
    compileStaticLib libFile oFiles (← getLeanAr)

/-- Build a shared library by linking the results of `linkJobs` using `leanc`. -/
def buildLeanSharedLib
  (libFile : FilePath) (linkJobs : Array (BuildJob FilePath))
  (weakArgs traceArgs : Array String := #[])
: SpawnM (BuildJob FilePath) :=
  let extraDepTrace :=
    return (← getLeanTrace).mix <| (pureHash traceArgs).mix platformTrace
  buildFileAfterDepArray libFile linkJobs (extraDepTrace := extraDepTrace) fun links => do
    compileSharedLib libFile (links.map toString ++ weakArgs ++ traceArgs) (← getLeanc)

/-- Build an executable by linking the results of `linkJobs` using `leanc`. -/
def buildLeanExe
  (exeFile : FilePath) (linkJobs : Array (BuildJob FilePath))
  (weakArgs traceArgs : Array String := #[])
: SpawnM (BuildJob FilePath) :=
  let extraDepTrace :=
    return (← getLeanTrace).mix <| (pureHash traceArgs).mix platformTrace
  buildFileAfterDepArray exeFile linkJobs (extraDepTrace := extraDepTrace) fun links => do
    compileExe exeFile links (weakArgs ++ traceArgs) (← getLeanc)

/-- Build a shared library from a static library using `leanc`. -/
def buildLeanSharedLibOfStatic
  (staticLibJob : BuildJob FilePath)
  (weakArgs traceArgs : Array String := #[])
: SpawnM (BuildJob FilePath) :=
  staticLibJob.bindSync fun staticLib staticTrace => do
    let dynlib := staticLib.withExtension sharedLibExt
    let baseArgs :=
      if System.Platform.isOSX then
        #[s!"-Wl,-force_load,{staticLib}"]
      else
        #["-Wl,--whole-archive", staticLib.toString, "-Wl,--no-whole-archive"]
    let depTrace := staticTrace.mix <|
      (← getLeanTrace).mix <| (pureHash traceArgs).mix <| platformTrace
    let args := baseArgs ++ weakArgs ++ traceArgs
    let trace ← buildFileUnlessUpToDate dynlib depTrace do
      compileSharedLib dynlib args (← getLeanc)
    return (dynlib, trace)

/-- Construct a `Dynlib` object for a shared library target. -/
def computeDynlibOfShared (sharedLibTarget : BuildJob FilePath) : SpawnM (BuildJob Dynlib) :=
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
