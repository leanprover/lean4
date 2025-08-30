/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lean.Data.Json
public import Lake.Build.Job.Monad
public import Lake.Config.Monad
import Lake.Util.IO
import Lake.Util.JsonObject
import Lake.Build.Target.Fetch
public import Lake.Build.Actions

/-! # Common Build Tools
This file defines general utilities that abstract common
build functionality and provides some common concrete build functions.
-/

open System Lean

namespace Lake

/-! ## General Utilities -/

public instance : MonadWorkspace JobM := inferInstance

open System.Platform in
/--
Build trace for the host platform.
If an artifact includes this trace, it is platform-dependent
and will be rebuilt on different host platforms.
-/
public def platformTrace : BuildTrace := .ofHash (pureHash target) target

/--
Mixes the platform into the current job's trace.
If an artifact includes this trace, it is platform-dependent
and will be rebuilt on different host platforms.
-/
@[inline] public def addPlatformTrace : JobM PUnit :=
  addTrace platformTrace

/-- Mixes Lean's trace into the current job's trace. -/
@[inline] public def addLeanTrace : JobM PUnit := do
  addTrace (← getLeanTrace)

/-- Mixes the trace of a pure value into the current job's trace. -/
@[inline] public def addPureTrace
  [ToString α] [ComputeHash α Id] (a : α) (caption := "pure")
: JobM PUnit := addTrace <| .ofHash (pureHash a) s!"{caption}: {toString a}"

/--
The build trace file format,
which stores information about a (successful) build.
-/
public structure BuildMetadata where
  depHash : Hash
  inputs : Array (String × Json)
  outputs? : Option Json
  log : Log
  /-- A trace file that was created from fetching an artifact from the cache. -/
  synthetic : Bool
  deriving ToJson

public protected def BuildMetadata.fromJson? (json : Json) : Except String BuildMetadata := do
  let obj ← JsonObject.fromJson? json
  let depHash ← obj.get "depHash"
  let inputs ← obj.getD "inputs" {}
  let outputs? ← obj.getD "outputs" none
  let log ← obj.getD "log" {}
  let synthetic ← obj.getD "synthetic" false
  return {depHash, inputs, outputs?, log, synthetic}

public instance : FromJson BuildMetadata := ⟨BuildMetadata.fromJson?⟩

/--
Construct build metadata from a trace stub.
That is, the old version of the trace file format that just contained a hash.
-/
public def BuildMetadata.ofStub (hash : Hash) : BuildMetadata :=
  {depHash := hash,  inputs := #[], outputs? := none, log := {}, synthetic := false}

@[deprecated ofStub (since := "2025-06-28")]
public abbrev BuildMetadata.ofHash := @ofStub

/-- Parse build metadata from a trace file's contents. -/
public def BuildMetadata.parse (contents : String) : Except String BuildMetadata :=
  if let some hash := Hash.ofString? contents.trim then
    return .ofStub hash
  else
    Json.parse contents >>= fromJson?

/-- Construct build metadata from a cached input-to-output mapping. -/
public def BuildMetadata.ofFetch (inputHash : Hash) (outputs : Json) : BuildMetadata :=
  {depHash := inputHash, outputs? := outputs, synthetic := true, inputs := #[], log := {}}

private partial def serializeInputs (inputs : Array BuildTrace) : Array (String × Json) :=
  inputs.foldl (init := {}) fun r trace =>
    let val :=
      if trace.inputs.isEmpty then
        toJson trace.hash
      else
        toJson (serializeInputs trace.inputs)
    r.push (trace.caption, val)

private def BuildMetadata.ofBuildCore
  (depTrace : BuildTrace) (outputs : Json) (log : Log)
: BuildMetadata where
  inputs := serializeInputs depTrace.inputs
  depHash := depTrace.hash
  outputs? := outputs
  synthetic := false
  log

/-- Construct trace file contents from a build's trace, outputs, and log. -/
@[inline] public def BuildMetadata.ofBuild
   [ToJson α]  (depTrace : BuildTrace) (outputs : α) (log : Log)
:= BuildMetadata.ofBuildCore depTrace (toJson outputs) log

/-- The state of the trace file data saved on the file system. -/
public inductive SavedTrace
| missing
| invalid
| ok (data : BuildMetadata)

/--
Try to read data from a trace file.
Logs if the read failed or the contents where invalid.
-/
public def readTraceFile (path : FilePath) : LogIO SavedTrace := do
  match (← IO.FS.readFile path |>.toBaseIO) with
  | .ok contents =>
    match BuildMetadata.parse contents with
    | .ok data => return .ok data
    | .error e => logVerbose s!"{path}: invalid trace file: {e}"; return .invalid
  | .error (.noFileOrDirectory ..) => return .missing
  | .error e => logWarning s!"{path}: read failed: {e}"; return .invalid

/--
Tries to read data from a trace file. On failure, returns `none`.
Logs if the read failed or the contents where invalid.
-/
@[inline, deprecated readTraceFile (since := "2025-06-26")]
public def readTraceFile? (path : FilePath) : LogIO (Option BuildMetadata) := do
  if let .ok data ← readTraceFile path then return some data else none

/-- Write a trace file containing the metadata. -/
public def BuildMetadata.writeFile (path : FilePath) (data : BuildMetadata) : IO Unit := do
  createParentDirs path
  IO.FS.writeFile path (toJson data).pretty

/-- Write a trace file containing metadata on an artifact fetched from a cache. -/
@[inline] public def writeFetchTrace (path : FilePath) (inputHash : Hash) (outputs : Json) : IO Unit :=
  BuildMetadata.writeFile path (.ofFetch inputHash outputs)

/-- Write a trace file containing metadata about a build. -/
@[inline] public def writeBuildTrace
  [ToJson α] (path : FilePath) (depTrace : BuildTrace) (outputs : α) (log : Log)
: IO Unit := BuildMetadata.writeFile path (.ofBuild depTrace outputs log)

@[deprecated writeBuildTrace (since := "2025-06-28")]
public abbrev writeTraceFile := @writeBuildTrace

/--
Checks if the `info` is up-to-date by comparing `depTrace` with `depHash`.
If old mode is enabled (e.g., `--old`), uses the `oldTrace` modification time
as the point of comparison instead.
-/
@[specialize] public def checkHashUpToDate
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

/-- Returns whether the hash does not match the trace's dependency hash. -/
public def SavedTrace.isDifferentFrom  (hash : Hash) (self : SavedTrace) : Bool :=
  match self with
  | .ok data =>
    hash != data.depHash
  | _ =>
    true

/--
Checks whether `info` is up-to-date with the trace.
If so, replays the log of the trace if available. -/
@[specialize] public def SavedTrace.replayIfUpToDate
  [CheckExists ι] [GetMTime ι]
  (info : ι) (depTrace : BuildTrace) (savedTrace : SavedTrace)
  (oldTrace := depTrace.mtime)
: JobM Bool := do
  match savedTrace with
  | .ok data =>
    if (← inline <| checkHashUpToDate info depTrace data.depHash oldTrace) then
      updateAction .replay
      data.log.replay
      return true
    else
      return false
  | .invalid =>
    return (← getIsOldMode) && (← oldTrace.checkUpToDate info)
  | .missing =>
    depTrace.checkAgainstTime info

/--
Replays the saved log from the trace if it exists and is not synthetic.
Otherwise, writes a new synthetic trace file recording the fetch of the artifact from the cache.
-/
public def SavedTrace.replayOrFetch
  (traceFile : FilePath) (inputHash : Hash) (outputs : Json) (savedTrace : SavedTrace)
: JobM Unit := do
  if let .ok data := savedTrace then
    if data.synthetic && data.log.isEmpty then
      updateAction .fetch
    else
      updateAction .replay
      data.log.replay
  else
    updateAction .fetch
    writeFetchTrace traceFile inputHash outputs

/-- **For internal use only.** -/
public class ToOutputJson (α : Type u) where
  toOutputJson (arts : α) : Json

public instance : ToOutputJson PUnit := ⟨fun _ => Json.null⟩
public instance : ToOutputJson Artifact := ⟨(toJson ·.toArtifactDescr)⟩

open ToOutputJson in
/--
Runs `build` as a build action of kind `action`.

The build's input trace (`depTrace`), JSON description of the result of `build`,
and log are saved to `traceFile`, if the build completes without a fatal error
(i.e., it does not `throw`).
-/
@[specialize] public def buildAction
  [ToOutputJson α]
  (depTrace : BuildTrace) (traceFile : FilePath) (build : JobM α)
  (action : JobAction := .build)
: JobM α := do
  if (← getNoBuild) then
    updateAction .build
    error "target is out-of-date and needs to be rebuilt"
  else
    updateAction action
    let startTime ← IO.monoMsNow
    try
      let iniPos ← getLogPos
      let a ← build -- fatal errors will abort here
      let log := (← getLog).takeFrom iniPos
      writeBuildTrace traceFile depTrace (toOutputJson a) log
      return a
    finally
      let endTime ← IO.monoMsNow
      let elapsed := endTime - startTime
      modify fun s => {s with buildTime := s.buildTime + elapsed}


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
@[inline] public def buildUnlessUpToDate?
  [CheckExists ι] [GetMTime ι] (info : ι)
  (depTrace : BuildTrace) (traceFile : FilePath) (build : JobM PUnit)
  (action : JobAction := .build) (oldTrace := depTrace.mtime)
: JobM Bool := do
  let savedTrace ← readTraceFile traceFile
  if (← savedTrace.replayIfUpToDate info depTrace oldTrace) then
    return true
  else
    buildAction depTrace traceFile build action
    return false

/--
Checks whether `info` is up-to-date, and runs `build` to recreate it if not.
If rebuilt, saves the new `depTrace` and build log to `traceFile`.

See `buildUnlessUpToDate?` for more details on how Lake determines whether
`info` is up-to-date.
-/
@[inline] public def buildUnlessUpToDate
  [CheckExists ι] [GetMTime ι] (info : ι)
  (depTrace : BuildTrace) (traceFile : FilePath) (build : JobM PUnit)
  (action : JobAction := .build) (oldTrace := depTrace.mtime)
: JobM PUnit := do
  discard <| buildUnlessUpToDate? info depTrace traceFile build action oldTrace

/-- Saves the hash of a file and to its `.hash` file. -/
public def writeFileHash (file : FilePath) (hash : Hash) : IO Unit := do
  let hashFile := FilePath.mk <| file.toString ++ ".hash"
  createParentDirs hashFile
  IO.FS.writeFile hashFile hash.toString

/--
Computes the hash of a file and saves it to a `.hash` file.

If `text := true`, `file` is hashed as a text file rather than a binary file.
-/
public def cacheFileHash (file : FilePath) (text := false) : IO Unit := do
  let hash ← computeFileHash file text
  writeFileHash file hash

/-- Remove the cached hash of a file (its `.hash` file) if it exists. -/
public def clearFileHash (file : FilePath) : IO Unit := do
  removeFileIfExists <| file.toString ++ ".hash"

/--
Fetches the hash of a file that may already be cached in a `.hash` file.
If hash files are not trusted (e.g., with `--rehash`) or the `.hash` file does
not exist, it will be created with a newly computed hash.

If `text := true`, `file` is hashed as a text file rather than a binary file.
-/
public def fetchFileHash (file : FilePath) (text := false) : JobM Hash := do
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
public def fetchFileTrace (file : FilePath) (text := false) : JobM BuildTrace := do
  let hash ← fetchFileHash file text
  let mtime ← getMTime file
  return {caption := file.toString, hash, mtime}

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
public def buildFileUnlessUpToDate'
  (file : FilePath) (build : JobM PUnit) (text := false)
: JobM Unit := do
  let traceFile := FilePath.mk <| file.toString ++ ".trace"
  buildUnlessUpToDate file (← getTrace) traceFile do
    build
    clearFileHash file
  setTrace (← fetchFileTrace file text)

/--
Copies `file` to the Lake cache with the file extension `ext`, and
saves its hash in its `.hash` file.

If `text := true`, `file` contents are hashed as a text file rather than a binary file.

If the Lake cache is disabled, the behavior of this function is undefined.
-/
public def Cache.saveArtifact
  (cache : Cache) (file : FilePath) (ext := "art") (text := false) (exe := false)
: IO Artifact := do
  if text then
    let contents ← IO.FS.readFile file
    let normalized := contents.crlfToLf
    let hash := Hash.ofString normalized
    let descr := artifactWithExt hash ext
    let path := cache.artifactDir / descr.toFilePath
    createParentDirs path
    IO.FS.writeFile path normalized
    writeFileHash file hash
    let mtime := (← getMTime path |>.toBaseIO).toOption.getD 0
    return {toArtifactDescr := descr, name := file.toString, path, mtime}
  else
    let contents ← IO.FS.readBinFile file
    let hash := Hash.ofByteArray contents
    let descr := artifactWithExt hash ext
    let path := cache.artifactDir / descr.toFilePath
    createParentDirs path
    IO.FS.writeBinFile path contents
    if exe then
      let r := ⟨true, true, true⟩
      IO.setAccessRights path ⟨r, r, r⟩ -- 777
    writeFileHash file hash
    let mtime := (← getMTime path |>.toBaseIO).toOption.getD 0
    return {toArtifactDescr := descr, name := file.toString, path, mtime}

@[inline,  inherit_doc Cache.saveArtifact]
public def cacheArtifact
  [MonadWorkspace m] [MonadLiftT IO m] [Monad m]
  (file : FilePath) (ext := "art") (text := false) (exe := false)
: m Artifact := do (← getLakeCache).saveArtifact file ext text exe

/-- **For internal use only.** -/
public class ResolveOutputs (m : Type v → Type w) (α : Type v) where
  resolveOutputs? (outputs : Json) : m (Option α)

open ResolveOutputs in
/--
Retrieve artifacts from the Lake cache using the the outputs stored
in either the saved trace file or in the cached input-to-content mapping.

**For internal use only.**
-/
@[specialize] public nonrec def getArtifacts?
  [ResolveOutputs JobM α]
  (inputHash : Hash) (traceFile : FilePath) (savedTrace : SavedTrace)
  (cache : Cache) (pkg : Package)
: JobM (Option α) := do
  let updateCache ← pkg.isArtifactCacheEnabled
  if let some out ← cache.readOutputs? pkg.cacheScope inputHash then
    if let some arts ← resolveOutputs? out then
      savedTrace.replayOrFetch traceFile inputHash out
      return some arts
    else
      logWarning s!"\
        input '{inputHash.toString.take 7}' found in package artifact cache, \
        but some output(s) were not"
  if let .ok data := savedTrace then
    if data.depHash == inputHash then
      if let some out := data.outputs? then
        if let some arts ← resolveOutputs? out then
          if updateCache then
            cache.writeOutputs pkg.cacheScope inputHash out
          savedTrace.replayOrFetch traceFile inputHash out
          return some arts
  return none

@[inline] def resolveArtifactsCore?
  [FromJson α] [MonadWorkspace m] [MonadLiftT BaseIO m] [MonadError m] [Monad m]
  (f : α → m (Option β)) (out : Json)
: m (Option β) := do
  match fromJson? out with
  | .ok (a : α) => f a
  | .error e => error e

@[inline] def resolveArtifact
  [MonadWorkspace m] [MonadLiftT BaseIO m] [MonadError m] [Monad m] (output : Json)
: m (Option Artifact) := resolveArtifactsCore? (do (← getLakeCache).getArtifact? ·) output

@[inline] def resolveOutput?
  [MonadWorkspace m] [MonadLiftT BaseIO m] [MonadError m] [Monad m] (output : Json)
: m (Option Artifact) := do
  match fromJson? output with
  | .ok descr => getArtifact? descr
  | .error e => error s!"unexpected output: {e}"

instance
  [MonadWorkspace m] [MonadLiftT BaseIO m] [MonadError m] [Monad m]
: ResolveOutputs m Artifact := ⟨resolveOutput?⟩

/--
Construct an artifact from a path outside the Lake artifact cache.

If `text := true`, `file` is hashed as a text file rather than a binary file.
-/
public def computeArtifact (path : FilePath) (ext := "art") (text := false) : JobM Artifact := do
  let hash ← fetchFileHash path text
  let mtime := (← getMTime path |>.toBaseIO).toOption.getD 0
  return {toArtifactDescr := artifactWithExt hash ext, name := path.toString, path, mtime}

/--
Uses the current job's trace to search Lake's local artifact cache for an artifact
with a matching extension (`ext`) and content hash. If one is found, use it.
Otherwise, builds `file` using `build` and saves it to the cache. If Lake's
local artifact cache is not enabled, falls back to `buildFileUnlessUpToDate'`.

If `text := true`, `file` is hashed as a text file rather than a binary file.

If `restore := true`, if `file` is missing but the artifact is in the cache,
it will be copied to the `file`. This function will also return `file` rather
than the path to the cached artifact.
-/
public def buildArtifactUnlessUpToDate
  (file : FilePath) (build : JobM PUnit)
  (text := false) (ext := "art") (restore := false) (exe := false)
: JobM Artifact := do
  let depTrace ← getTrace
  let traceFile := FilePath.mk <| file.toString ++ ".trace"
  let savedTrace ← readTraceFile traceFile
  if let some pkg ← getCurrPackage? then
    let cache ← getLakeCache
    let inputHash := depTrace.hash
    let fetchArt? restore := do
      let some (art : Artifact) ← getArtifacts? inputHash traceFile savedTrace cache pkg
        | return none
      if restore then
        if savedTrace.isDifferentFrom inputHash || !(← file.pathExists) then
          logVerbose s!"restored artifact from cache to: {file}"
          copyFile art.path file
          if exe then
            let r := ⟨true, true, true⟩
            IO.setAccessRights file ⟨r, r, r⟩ -- 777
          writeFileHash file art.hash
        return some (art.useLocalFile file)
      else
        return some art
    if (← pkg.isArtifactCacheEnabled) then
      if let some art ← fetchArt? restore then
        setTrace art.trace
        if let some outputsRef := pkg.outputsRef? then
          outputsRef.insert inputHash art.hash
        return art
      else
        unless (← savedTrace.replayIfUpToDate file depTrace) do
          discard <| doBuild depTrace traceFile
        let art ← cacheArtifact file ext text exe
        cache.writeOutputs pkg.cacheScope inputHash art.toArtifactDescr
        if let some outputsRef := pkg.outputsRef? then
          outputsRef.insert inputHash art.toArtifactDescr
        setTrace art.trace
        return if restore then art.useLocalFile file else art
    else
      let art ← id do
        if (← savedTrace.replayIfUpToDate file depTrace) then
          computeArtifact file ext
        else if let some art ← fetchArt? (restore := true) then
          return art
        else
          doBuild depTrace traceFile
      if let some outputsRef := pkg.outputsRef? then
        outputsRef.insert inputHash art.toArtifactDescr
      setTrace art.trace
      return art
  else
    let art ←
      if (← savedTrace.replayIfUpToDate file depTrace) then
        computeArtifact file ext text
      else
        doBuild depTrace traceFile
    setTrace art.trace
    return art
where
  doBuild depTrace traceFile :=
    inline <| buildAction depTrace traceFile do
      build
      clearFileHash file
      removeFileIfExists traceFile
      computeArtifact file ext

/--
Build `file` using `build` after `dep` completes if the dependency's
trace (and/or `extraDepTrace`) has changed.

If `text := true`, `file` is handled as a text file rather than a binary file.
-/
@[inline] public def buildFileAfterDep
  (file : FilePath) (dep : Job α) (build : α → JobM PUnit)
  (extraDepTrace : JobM _ := pure BuildTrace.nil) (text := false)
: SpawnM (Job FilePath) :=
  dep.mapM fun depInfo => do
    addTrace (← extraDepTrace)
    let art ← buildArtifactUnlessUpToDate file (build depInfo) text
    return art.path

/-! ## Common Builds -/

/--
A build job for a binary file that is expected to already exist (e.g., a data blob).

Any byte difference in a binary file will trigger a rebuild of its dependents.
-/
public def inputBinFile (path : FilePath) : SpawnM (Job FilePath) := Job.async do
  setTrace (← computeTrace path)
  return path

/--
A build job for a text file that is expected to already exist (e.g., a source file).

Text file traces have normalized line endings to avoid unnecessary rebuilds across platforms.
-/
public def inputTextFile (path : FilePath) : SpawnM (Job FilePath) := Job.async do
  setTrace (← computeTrace (TextFilePath.mk path))
  return path

/--
A build job for a file that is expected to already exist (e.g., a data blob or source file).

If `text := true`, the file is handled as a text file rather than a binary file.
Any byte difference in a binary file will trigger a rebuild of its dependents.
In contrast, text file traces have normalized line endings to avoid unnecessary
rebuilds across platforms.
-/
@[inline] public def inputFile (path : FilePath) (text : Bool) : SpawnM (Job FilePath) :=
  if text then inputTextFile path else inputBinFile path

/--
A build job for a directory of files that are expected to already exist.
Returns an array of the files in the directory that match the filter.

If `text := true`, the files are handled as text files rather than a binary files.
Any byte difference in a binary file will trigger a rebuild of its dependents.
In contrast, text file traces have normalized line endings to avoid unnecessary
rebuilds across platforms.
-/
public def inputDir
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
@[inline] public def buildO
  (oFile : FilePath) (srcJob : Job FilePath)
  (weakArgs traceArgs : Array String := #[]) (compiler : FilePath := "cc")
  (extraDepTrace : JobM _ := pure BuildTrace.nil)
: SpawnM (Job FilePath) :=
  srcJob.mapM fun srcFile => do
    addPlatformTrace -- object files are platform-dependent artifacts
    addPureTrace traceArgs "traceArgs"
    addTrace (← extraDepTrace)
    let art ← buildArtifactUnlessUpToDate oFile (ext := "o") do
      compileO oFile srcFile (weakArgs ++ traceArgs) compiler
    return art.path

/--
Build an object file from a source fie job (i.e, a `lean -c` output)
using the Lean toolchain's C compiler.
-/
public def buildLeanO
  (oFile : FilePath) (srcJob : Job FilePath)
  (weakArgs traceArgs : Array String := #[])
  (leanIncludeDir? : Option FilePath := none)
: SpawnM (Job FilePath) :=
  srcJob.mapM fun srcFile => do
    addLeanTrace
    addPureTrace traceArgs "traceArgs"
    addPlatformTrace -- object files are platform-dependent artifacts
    let art ← buildArtifactUnlessUpToDate oFile (ext := "o") do
      let lean ← getLeanInstall
      let includeDir := leanIncludeDir?.getD lean.includeDir
      let args := #["-I", includeDir.toString] ++ lean.ccFlags ++ weakArgs ++ traceArgs
      compileO oFile srcFile args lean.cc
    return art.path

/-- Build a static library from object file jobs using the Lean toolchain's `ar`. -/
public def buildStaticLib
  (libFile : FilePath) (oFileJobs : Array (Job FilePath)) (thin :=  false)
: SpawnM (Job FilePath) :=
  (Job.collectArray oFileJobs "objs").mapM fun oFiles => do
    let art ← buildArtifactUnlessUpToDate libFile (ext := "a") (restore := true) do
      compileStaticLib libFile oFiles (← getLeanAr) thin
    return art.path

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
  go lib (ps : List String) (v : Std.TreeSet String compare) (o : Array Dynlib) := do
    let o := o.push lib
    if v.contains lib.name then
      return (v, o)
    if ps.contains lib.name then
      throw (lib.name :: ps)
    let ps := lib.name :: ps
    let v := v.insert lib.name
    let (v, o) ← lib.deps.foldlM (init := (v, o)) fun (v, o) lib =>
      go lib ps v o
    return (v, o)

/--
Build a shared library by linking the results of `linkJobs`
using the Lean toolchain's C compiler.
-/
public def buildSharedLib
  (libName : String) (libFile : FilePath)
  (linkObjs : Array (Job FilePath)) (linkLibs : Array (Job Dynlib))
  (weakArgs traceArgs : Array String := #[]) (linker := "c++")
  (extraDepTrace : JobM _ := pure BuildTrace.nil)
  (plugin := false) (linkDeps := Platform.isWindows)
: SpawnM (Job Dynlib) :=
  (Job.collectArray linkObjs "linkObjs").bindM (sync := true) fun objs => do
  (Job.collectArray linkLibs "linkLibs").mapM fun libs => do
    addPureTrace traceArgs "traceArgs"
    addPlatformTrace -- shared libraries are platform-dependent artifacts
    addTrace (← extraDepTrace)
    -- Lean plugins are required to have a specific name
    -- and thus need to copied from the cache with that name
    let art ← buildArtifactUnlessUpToDate libFile (ext := sharedLibExt) (restore := true) do
      let libs ← if linkDeps then mkLinkOrder libs else pure #[]
      let args := mkLinkObjArgs objs libs ++ weakArgs ++ traceArgs
      compileSharedLib libFile args linker
    return {name := libName, path := art.path, deps := libs, plugin}

/--
Build a shared library by linking the results of `linkJobs`
using `linker`.
-/
public def buildLeanSharedLib
  (libName : String) (libFile : FilePath)
  (linkObjs : Array (Job FilePath)) (linkLibs : Array (Job Dynlib))
  (weakArgs traceArgs : Array String := #[]) (plugin := false)
  (linkDeps := Platform.isWindows)
: SpawnM (Job Dynlib) :=
  (Job.collectArray linkObjs "linkObjs").bindM (sync := true) fun objs => do
  (Job.collectArray linkLibs "linkLibs").mapM fun libs => do
    addLeanTrace
    addPureTrace traceArgs "traceArgs"
    addPlatformTrace -- shared libraries are platform-dependent artifacts
    -- Lean plugins are required to have a specific name
    -- and thus need to copied from the cache with that name
    let art ← buildArtifactUnlessUpToDate libFile (ext := sharedLibExt) (restore := true) do
      let lean ← getLeanInstall
      let libs ← if linkDeps then mkLinkOrder libs else pure #[]
      let args := mkLinkObjArgs objs libs ++ weakArgs ++ traceArgs ++
        #["-L", lean.leanLibDir.toString] ++ lean.ccLinkSharedFlags
      compileSharedLib libFile args lean.cc
    return {name := libName, path := art.path, deps := libs, plugin}

/--
Build an executable by linking the results of `linkJobs`
using the Lean toolchain's linker.
-/
public def buildLeanExe
  (exeFile : FilePath)
  (linkObjs : Array (Job FilePath)) (linkLibs : Array (Job Dynlib))
  (weakArgs traceArgs : Array String := #[]) (sharedLean : Bool := false)
: SpawnM (Job FilePath) :=
  (Job.collectArray linkObjs "linkObjs").bindM (sync := true) fun objs => do
  (Job.collectArray linkLibs "linkLibs").mapM fun libs => do
    addLeanTrace
    addPureTrace traceArgs "traceArgs"
    addPlatformTrace -- executables are platform-dependent artifacts
    let art ← buildArtifactUnlessUpToDate exeFile (ext := FilePath.exeExtension) (exe := true) (restore := true) do
      let lean ← getLeanInstall
      let libs ← mkLinkOrder libs
      let args := mkLinkObjArgs objs libs ++ weakArgs ++ traceArgs ++
        #["-L", lean.leanLibDir.toString] ++ lean.ccLinkFlags sharedLean
      compileExe exeFile args lean.cc
    return art.path
