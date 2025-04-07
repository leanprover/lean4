/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Config.Monad
import Lake.Util.JsonObject
import Lake.Build.Target.Fetch
import Lake.Build.Actions
import Lake.Build.Job

/-! # Common Build Tools
This file defines general utilities that abstract common
build functionality and provides some common concrete build functions.
-/

open System Lean

namespace Lake

/-! ## General Utilities -/

/-- Exit code to return if `--no-build` is set and a build is required. -/
def noBuildCode : ExitCode := 3

/--
Build trace for the host platform.
If an artifact includes this trace, it is platform-dependent
and will be rebuilt on different host platforms.
-/
def platformTrace := pureHash System.Platform.target

/--
Mixes the platform into the current job's trace.
If an artifact includes this trace, it is platform-dependent
and will be rebuilt on different host platforms.
-/
@[inline] def addPlatformTrace : JobM PUnit :=
  addTrace platformTrace

/-- Mixes Lean's trace into the current job's trace. -/
@[inline] def addLeanTrace : JobM PUnit := do
  addTrace (← getLeanTrace)

/-- Mixes the trace of a pure value into the current job's trace. -/
@[inline] def addPureTrace [ComputeHash α Id] (a : α) : JobM PUnit := do
  addTrace (pureHash a)

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
Builds `file` using `build` unless it already exists and the current job's
trace matches the trace stored in the `.trace` file. If built, saves the new
trace and caches `file`'s hash in a `.hash` file. Otherwise, tries to fetch the
hash from the `.hash` file using `fetchFileTrace`. Build logs (if any) are
saved to the trace file and replayed from there if the build is skipped.

For example, given `file := "foo.c"`, compares `getTrace` with that in
`foo.c.trace`. If built, the hash is cached in `foo.c.hash` and the new
trace is saved to `foo.c.trace` (including the build log).

If `text := true`, `file` is hashed as a text file rather than a binary file.
-/
def buildFileUnlessUpToDate'
  (file : FilePath) (build : JobM PUnit) (text := false)
: JobM Unit := do
  let traceFile := FilePath.mk <| file.toString ++ ".trace"
  buildUnlessUpToDate file (← getTrace) traceFile do
    build
    clearFileHash file
  setTrace (← fetchFileTrace file text)

@[deprecated buildFileUnlessUpToDate' (since := "2024-12-06")]
abbrev buildFileUnlessUpToDate
  (file : FilePath) (depTrace : BuildTrace) (build : JobM PUnit) (text := false)
: JobM BuildTrace := do
  setTrace depTrace
  buildFileUnlessUpToDate' file build text
  getTrace

/--
Build `file` using `build` after `dep` completes if the dependency's
trace (and/or `extraDepTrace`) has changed.

If `text := true`, `file` is handled as a text file rather than a binary file.
-/
@[inline] def buildFileAfterDep
  (file : FilePath) (dep : Job α) (build : α → JobM PUnit)
  (extraDepTrace : JobM _ := pure BuildTrace.nil) (text := false)
: SpawnM (Job FilePath) :=
  dep.mapM fun depInfo => do
    addTrace (← extraDepTrace)
    buildFileUnlessUpToDate' file (build depInfo) text
    return file

/--
Build `file` using `build` after `deps` have built if any of their traces change.

If `text := true`, `file` is handled as a text file rather than a binary file.
-/
@[inline, deprecated buildFileAfterDep (since := "2024-12-06")]
abbrev buildFileAfterDepList
  (file : FilePath) (deps : List (Job α)) (build : List α → JobM PUnit)
  (extraDepTrace : JobM _ := pure BuildTrace.nil) (text := false)
: SpawnM (Job FilePath) := do
  buildFileAfterDep file (.collectList deps) build extraDepTrace text

/--
Build `file` using `build` after `deps` have built if any of their traces change.

If `text := true`, `file` is handled as a text file rather than a binary file.
-/
@[inline, deprecated buildFileAfterDep (since := "2024-12-06")]
def buildFileAfterDepArray
  (file : FilePath) (deps : Array (Job α)) (build : Array α → JobM PUnit)
  (extraDepTrace : JobM _ := pure BuildTrace.nil) (text := false)
: SpawnM (Job FilePath) := do
  buildFileAfterDep file (.collectArray deps) build extraDepTrace text

/-! ## Common Builds -/

/--
A build job for binary file that is expected to already exist (e.g., a data blob).

Any byte difference in a binary file will trigger a rebuild of its dependents.
-/
def inputBinFile (path : FilePath) : SpawnM (Job FilePath) := Job.async do
  setTrace (← computeTrace path)
  return path

/--
A build job for text file that is expected to already exist (e.g., a source file).

Text file traces have normalized line endings to avoid unnecessary rebuilds across platforms.
-/
def inputTextFile (path : FilePath) : SpawnM (Job FilePath) := Job.async do
  setTrace (← computeTrace (TextFilePath.mk path))
  return path

/--
A build job for file that is expected to already exist  (e.g., a data blob or source file).

If `text := true`, the file is handled as a text file rather than a binary file.
Any byte difference in a binary file will trigger a rebuild of its dependents.
In contrast, text file traces have normalized line endings to avoid unnecessary
rebuilds across platforms.
-/
@[inline] def inputFile (path : FilePath) (text : Bool) : SpawnM (Job FilePath) :=
  if text then inputTextFile path else inputBinFile path

/--
A build job for a directory of files that are expected to already exist.
Returns an array of the files in the directory that match the filter.

If `text := true`, the files are handled as text files rather than a binary files.
Any byte difference in a binary file will trigger a rebuild of its dependents.
In contrast, text file traces have normalized line endings to avoid unnecessary
rebuilds across platforms.
-/
def inputDir
  (path : FilePath) (text : Bool) (filter : FilePath → Bool)
: SpawnM (Job (Array FilePath)) := do
  let job ← Job.async do
    let fs ← path.readDir
    let ps := fs.filterMap fun f =>
      if filter f.path then some f.path else none
    -- Makes the order of files consistent across platforms
    let ps := ps.qsort (toString · < toString ·)
    return ps
  job.bindM fun ps =>
    Job.collectArray <$> ps.mapM (inputFile · text)

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
which will be computed in the resulting `Job` before building.
-/
@[inline] def buildO
  (oFile : FilePath) (srcJob : Job FilePath)
  (weakArgs traceArgs : Array String := #[]) (compiler : FilePath := "cc")
  (extraDepTrace : JobM _ := pure BuildTrace.nil)
: SpawnM (Job FilePath) :=
  srcJob.mapM fun srcFile => do
    addPlatformTrace -- object files are platform-dependent artifacts
    addPureTrace traceArgs
    addTrace (← extraDepTrace)
    buildFileUnlessUpToDate' oFile do
      compileO oFile srcFile (weakArgs ++ traceArgs) compiler
    return oFile

/--
Build an object file from a source fie job (i.e, a `lean -c` output)=
using the Lean toolchain's C compiler.
-/
def buildLeanO
  (oFile : FilePath) (srcJob : Job FilePath)
  (weakArgs traceArgs : Array String := #[])
: SpawnM (Job FilePath) :=
  srcJob.mapM fun srcFile => do
    addLeanTrace
    addPureTrace traceArgs
    addPlatformTrace -- object files are platform-dependent artifacts
    buildFileUnlessUpToDate' oFile do
      let lean ← getLeanInstall
      compileO oFile srcFile (lean.ccFlags ++ weakArgs ++ traceArgs) lean.cc
    return oFile

/-- Build a static library from object file jobs using the Lean toolchain's `ar`. -/
def buildStaticLib
  (libFile : FilePath) (oFileJobs : Array (Job FilePath)) (thin :=  false)
: SpawnM (Job FilePath) :=
  (Job.collectArray oFileJobs).mapM fun oFiles => do
    buildFileUnlessUpToDate' libFile do
      compileStaticLib libFile oFiles (← getLeanAr) thin
    return libFile

private def mkLinkObjArgs
  (objs : Array FilePath) (libs : Array Dynlib) : Array String
:= Id.run do
  let mut args := #[]
  for obj in objs do
    args := args.push obj.toString
  for lib in libs do
    if let some dir := lib.dir? then
      args := args.push s!"-L{dir}"
    args := args.push s!"-l{lib.name}"
  return args

/--
Topologically sorts the library dependency tree by name.
Libraries come *before* their dependencies.
-/
private partial def mkLinkOrder (libs : Array Dynlib) : JobM (Array Dynlib) := do
  let r := libs.foldlM (m := Except (Cycle String)) (init := ({}, #[])) fun (v, o) lib =>
    go lib [] v o
  match r with
  | .ok (_, order) => pure order
  | .error cycle => error s!"library dependency cycle:\n{formatCycle cycle}"
where
  go lib (ps : List String) (v : RBMap String Unit compare) (o : Array Dynlib) := do
    let o := o.push lib
    if v.contains lib.name then
      return (v, o)
    if ps.contains lib.name then
      throw (lib.name :: ps)
    let ps := lib.name :: ps
    let v := v.insert lib.name ()
    let (v, o) ← lib.deps.foldlM (init := (v, o)) fun (v, o) lib =>
      go lib ps v o
    return (v, o)

/--
Build a shared library by linking the results of `linkJobs`
using the Lean toolchain's C compiler.
-/
def buildSharedLib
  (libName : String) (libFile : FilePath)
  (linkObjs : Array (Job FilePath)) (linkLibs : Array (Job Dynlib))
  (weakArgs traceArgs : Array String := #[]) (linker := "c++")
  (extraDepTrace : JobM _ := pure BuildTrace.nil)
  (plugin := false) (linkDeps := Platform.isWindows)
: SpawnM (Job Dynlib) :=
  (Job.collectArray linkObjs).bindM fun objs => do
  (Job.collectArray linkLibs).mapM (sync := true) fun libs => do
    addPureTrace traceArgs
    addPlatformTrace -- shared libraries are platform-dependent artifacts
    addTrace (← extraDepTrace)
    buildFileUnlessUpToDate' libFile do
      let libs ← if linkDeps then mkLinkOrder libs else pure #[]
      let args := mkLinkObjArgs objs libs ++ weakArgs ++ traceArgs
      compileSharedLib libFile args linker
    return {name := libName, path := libFile, deps := libs, plugin}

/--
Build a shared library by linking the results of `linkJobs`
using `linker`.
-/
def buildLeanSharedLib
  (libName : String) (libFile : FilePath)
  (linkObjs : Array (Job FilePath)) (linkLibs : Array (Job Dynlib))
  (weakArgs traceArgs : Array String := #[]) (plugin := false)
  (linkDeps := Platform.isWindows)
: SpawnM (Job Dynlib) :=
  (Job.collectArray linkObjs).bindM fun objs => do
  (Job.collectArray linkLibs).mapM (sync := true) fun libs => do
    addLeanTrace
    addPureTrace traceArgs
    addPlatformTrace -- shared libraries are platform-dependent artifacts
    buildFileUnlessUpToDate' libFile do
      let lean ← getLeanInstall
      let libs ← if linkDeps then mkLinkOrder libs else pure #[]
      let args := mkLinkObjArgs objs libs ++
        weakArgs ++ traceArgs ++ lean.ccLinkSharedFlags
      compileSharedLib libFile args lean.cc
    return {name := libName, path := libFile, deps := libs, plugin}

/--
Build an executable by linking the results of `linkJobs`
using the Lean toolchain's linker.
-/
def buildLeanExe
  (exeFile : FilePath)
  (linkObjs : Array (Job FilePath)) (linkLibs : Array (Job Dynlib))
  (weakArgs traceArgs : Array String := #[]) (sharedLean : Bool := false)
: SpawnM (Job FilePath) :=
  (Job.collectArray linkObjs).bindM fun objs => do
  (Job.collectArray linkLibs).mapM (sync := true) fun libs => do
    addLeanTrace
    addPureTrace traceArgs
    addPlatformTrace -- executables are platform-dependent artifacts
    buildFileUnlessUpToDate' exeFile do
      let lean ← getLeanInstall
      let libs ← mkLinkOrder libs
      let args := mkLinkObjArgs objs libs ++
        weakArgs ++ traceArgs ++ lean.ccLinkFlags sharedLean
      compileExe exeFile args lean.cc
    return exeFile
