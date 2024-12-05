/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Config.Monad
import Lake.Build.Actions
import Lake.Util.JsonObject

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

/--
The build trace file format,
which stores information about a (successful) build.
-/
structure BuildMetadata where
  depHash : Hash
  log : Log
  deriving ToJson

def BuildMetadata.ofHash (h : Hash) : BuildMetadata :=
  {depHash := h, log := {}}

def BuildMetadata.fromJson? (json : Json) : Except String BuildMetadata := do
  let obj ← JsonObject.fromJson? json
  let depHash ← obj.get "depHash"
  let log ← obj.getD "log" {}
  return {depHash, log}

instance : FromJson BuildMetadata := ⟨BuildMetadata.fromJson?⟩

/-- Read persistent trace data from a file. -/
def readTraceFile? (path : FilePath) : LogIO (Option BuildMetadata) := OptionT.run do
  match (← IO.FS.readFile path |>.toBaseIO) with
  | .ok contents =>
    if let some hash := Hash.ofString? contents.trim then
      return .ofHash hash
    else
      match Json.parse contents >>= fromJson? with
      | .ok contents => return contents
      | .error e => logVerbose s!"{path}: invalid trace file: {e}"; failure
  | .error (.noFileOrDirectory ..) => failure
  | .error e => logWarning s!"{path}: read failed: {e}"; failure

/-- Write persistent trace data to a file. -/
def writeTraceFile (path : FilePath) (depTrace : BuildTrace) (log : Log) := do
  createParentDirs path
  let data := {log, depHash := depTrace.hash : BuildMetadata}
  IO.FS.writeFile path (toJson data).pretty

/--
Checks if the `info` is up-to-date by comparing `depTrace` with `depHash`.
If old mode is enabled (e.g., `--old`), uses the `oldTrace` modification time
as the point of comparison instead.
-/
@[specialize] def checkHashUpToDate
  [CheckExists ι] [GetMTime ι]
  (info : ι) (depTrace : BuildTrace) (depHash : Option Hash)
  (oldTrace := depTrace.mtime)
: JobM Bool := do
  if depTrace.hash == depHash then
    checkExists info
  else if (← getIsOldMode) then
    oldTrace.checkUpToDate info
  else
    return false

/--
Checks whether `info` is up-to-date, and runs `build` to recreate it if not.
If rebuilt, saves the new `depTrace` and build log to `traceFile`.
Returns whether `info` was already up-to-date.

**Up-to-date Checking**

If `traceFile` exists, checks that the hash in `depTrace` matches that
of the `traceFile`. If not, and old mode is enabled (e.g., `--old`), falls back
to the `oldTrace` modification time as the point of comparison.
If up-to-date, replay the build log stored in `traceFile`.

If `traceFile` does not exist, checks that `info` has a newer modification time
then `depTrace` / `oldTrace`. No log will be replayed.
-/
@[specialize] def buildUnlessUpToDate?
  [CheckExists ι] [GetMTime ι] (info : ι)
  (depTrace : BuildTrace) (traceFile : FilePath) (build : JobM PUnit)
  (action : JobAction := .build) (oldTrace := depTrace.mtime)
: JobM Bool := do
  if (← traceFile.pathExists) then
    if let some data ← readTraceFile? traceFile then
      if (← checkHashUpToDate info depTrace data.depHash oldTrace) then
        updateAction .replay
        data.log.replay
        return true
      else
        go
    else if (← getIsOldMode) && (← oldTrace.checkUpToDate info) then
      return true
    else
      go
  else
    if (← depTrace.checkAgainstTime info) then
      return true
    else
      go
where
  go := do
    if (← getNoBuild) then
      IO.Process.exit noBuildCode.toUInt8
    else
      updateAction action
      let iniPos ← getLogPos
      build -- fatal errors will not produce a trace (or cache their log)
      let log := (← getLog).takeFrom iniPos
      writeTraceFile traceFile depTrace log
      return false

/--
Checks whether `info` is up-to-date, and runs `build` to recreate it if not.
If rebuilt, saves the new `depTrace` and build log to `traceFile`.

See `buildUnlessUpToDate?` for more details on how Lake determines whether
`info` is up-to-date.
-/
@[inline] def buildUnlessUpToDate
  [CheckExists ι] [GetMTime ι] (info : ι)
  (depTrace : BuildTrace) (traceFile : FilePath) (build : JobM PUnit)
  (action : JobAction := .build) (oldTrace := depTrace.mtime)
: JobM PUnit := do
  discard <| buildUnlessUpToDate? info depTrace traceFile build action oldTrace

/-- Computes the hash of a file and saves it to a `.hash` file. -/
def cacheFileHash (file : FilePath) : IO Unit := do
  let hash ← computeHash file
  let hashFile := FilePath.mk <| file.toString ++ ".hash"
  createParentDirs hashFile
  IO.FS.writeFile hashFile hash.toString

/-- Remove the cached hash of a file (its `.hash` file). -/
def clearFileHash (file : FilePath) : IO Unit := do
  try
    IO.FS.removeFile <| file.toString ++ ".hash"
  catch
    | .noFileOrDirectory .. => pure ()
    | e => throw e

/--
Fetches the hash of a file that may already be cached in a `.hash` file.
If hash files are not trusted (e.g., with `--rehash`) or the `.hash` file does
not exist, it will be created with a newly computed hash.

If `text := true`, `file` is hashed as a text file rather than a binary file.
-/
def fetchFileHash (file : FilePath) (text := false) : JobM Hash := do
  let hashFile := FilePath.mk <| file.toString ++ ".hash"
  if (← getTrustHash) then
    if let some hash ← Hash.load? hashFile then
      return hash
  let hash ← computeFileHash file text
  createParentDirs hashFile
  IO.FS.writeFile hashFile hash.toString
  return hash

/--
Fetches the trace of a file that may have already have its hash cached
in a `.hash` file. If no such `.hash` file exists, recomputes and creates it.

If `text := true`, `file` is hashed as text file rather than a binary file.
-/
def fetchFileTrace (file : FilePath) (text := false) : JobM BuildTrace := do
  return .mk (← fetchFileHash file text) (← getMTime file)

/--
Builds `file` using `build` unless it already exists and `depTrace` matches
the trace stored in the `.trace` file. If built, save the new `depTrace` and
cache `file`'s hash in a `.hash` file. Otherwise, try to fetch the hash from
the `.hash` file using `fetchFileTrace`. Build logs (if any) are saved to
a `.log.json` file and replayed from there if the build is skipped.

For example, given `file := "foo.c"`, compares `depTrace` with that in
`foo.c.trace` with the hash cached in `foo.c.hash` and the log cached in
`foo.c.trace`.

If `text := true`, `file` is hashed as a text file rather than a binary file.
-/
def buildFileUnlessUpToDate
  (file : FilePath) (depTrace : BuildTrace) (build : JobM PUnit) (text := false)
: JobM BuildTrace := do
  let traceFile := FilePath.mk <| file.toString ++ ".trace"
  buildUnlessUpToDate file depTrace traceFile do
    build
    clearFileHash file
  fetchFileTrace file text

/--
Build `file` using `build` after `dep` completes if the dependency's
trace (and/or `extraDepTrace`) has changed.

If `text := true`, `file` is handled as a text file rather than a binary file.
-/
@[inline] def buildFileAfterDep
  (file : FilePath) (dep : BuildJob α) (build : α → JobM PUnit)
  (extraDepTrace : JobM _ := pure BuildTrace.nil) (text := false)
: SpawnM (BuildJob FilePath) :=
  dep.bindSync fun depInfo depTrace => do
    let depTrace := depTrace.mix (← extraDepTrace)
    let trace ← buildFileUnlessUpToDate file depTrace (build depInfo) text
    return (file, trace)

/--
Build `file` using `build` after `deps` have built if any of their traces change.

If `text := true`, `file` is handled as a text file rather than a binary file.
-/
@[inline] def buildFileAfterDepList
  (file : FilePath) (deps : List (BuildJob α)) (build : List α → JobM PUnit)
  (extraDepTrace : JobM _ := pure BuildTrace.nil) (text := false)
: SpawnM (BuildJob FilePath) := do
  buildFileAfterDep file (.collectList deps) build extraDepTrace text

/--
Build `file` using `build` after `deps` have built if any of their traces change.

If `text := true`, `file` is handled as a text file rather than a binary file.
-/
@[inline] def buildFileAfterDepArray
  (file : FilePath) (deps : Array (BuildJob α)) (build : Array α → JobM PUnit)
  (extraDepTrace : JobM _ := pure BuildTrace.nil) (text := false)
: SpawnM (BuildJob FilePath) := do
  buildFileAfterDep file (.collectArray deps) build extraDepTrace text

/-! ## Common Builds -/

/--
A build job for binary file that is expected to already exist (e.g., a data blob).

Any byte difference in a binary file will trigger a rebuild of its dependents.
-/
def inputBinFile (path : FilePath) : SpawnM (BuildJob FilePath) :=
  Job.async <| (path, ·) <$> computeTrace path

/--
A build job for text file that is expected to already exist (e.g., a source file).

Text file traces have normalized line endings to avoid unnecessary rebuilds across platforms.
-/
def inputTextFile (path : FilePath) : SpawnM (BuildJob FilePath) :=
  Job.async <| (path, ·) <$> computeTrace (TextFilePath.mk path)

/--
A build job for file that is expected to already exist  (e.g., a data blob or source file).

If `text := true`, the file is handled as a text file rather than a binary file.
Any byte difference in a binary file will trigger a rebuild of its dependents.
In contrast, text file traces have normalized line endings to avoid unnecessary
rebuilds across platforms.
-/
@[inline] def inputFile (path : FilePath) (text : Bool) : SpawnM (BuildJob FilePath) :=
  if text then inputTextFile path else inputBinFile path

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
    let lean ← getLeanInstall
    compileO oFile srcFile (lean.ccFlags ++ weakArgs ++ traceArgs) lean.cc

/-- Build a static library from object file jobs using the `ar` packaged with Lean. -/
def buildStaticLib
  (libFile : FilePath) (oFileJobs : Array (BuildJob FilePath))
: SpawnM (BuildJob FilePath) :=
  buildFileAfterDepArray libFile oFileJobs fun oFiles => do
    compileStaticLib libFile oFiles (← getLeanAr)

/--
Build a shared library by linking the results of `linkJobs`
using the Lean toolchain's C compiler.
-/
def buildLeanSharedLib
  (libFile : FilePath) (linkJobs : Array (BuildJob FilePath))
  (weakArgs traceArgs : Array String := #[])
: SpawnM (BuildJob FilePath) :=
  let extraDepTrace :=
    return (← getLeanTrace).mix <| (pureHash traceArgs).mix platformTrace
  buildFileAfterDepArray libFile linkJobs (extraDepTrace := extraDepTrace) fun links => do
    let lean ← getLeanInstall
    let args := links.map toString ++ weakArgs ++ traceArgs ++ lean.ccLinkSharedFlags
    compileSharedLib libFile args lean.cc


/--
Build an executable by linking the results of `linkJobs`
using the Lean toolchain's linker.
-/
def buildLeanExe
  (exeFile : FilePath) (linkJobs : Array (BuildJob FilePath))
  (weakArgs traceArgs : Array String := #[]) (sharedLean : Bool := false)
: SpawnM (BuildJob FilePath) :=
  let extraDepTrace :=
    return (← getLeanTrace).mix <|
      (pureHash sharedLean).mix <| (pureHash traceArgs).mix platformTrace
  buildFileAfterDepArray exeFile linkJobs (extraDepTrace := extraDepTrace) fun links => do
    let lean ← getLeanInstall
    let args := weakArgs ++ traceArgs ++ lean.ccLinkFlags sharedLean
    compileExe exeFile links args lean.cc

/--
Build a shared library from a static library using `leanc`
using the Lean toolchain's linker.
-/
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
    let lean ← getLeanInstall
    let depTrace := staticTrace.mix <|
      (← getLeanTrace).mix <| (pureHash traceArgs).mix <| platformTrace
    let args := baseArgs ++ weakArgs ++ traceArgs ++ lean.ccLinkSharedFlags
    let trace ← buildFileUnlessUpToDate dynlib depTrace do
      compileSharedLib dynlib args lean.cc
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
