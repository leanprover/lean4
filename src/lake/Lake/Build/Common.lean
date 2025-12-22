/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Build.Job.Monad
public import Lake.Config.Monad
public import Lake.Util.JsonObject
public import Lake.Util.IO
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

/-- The current version of the trace file format. -/
def BuildMetadata.schemaVersion : String := "2025-09-10"

public protected def BuildMetadata.toJson (self : BuildMetadata) : Json :=
  ({} : JsonObject)
  |>.insert "schemaVersion" schemaVersion
  |>.insert "depHash" self.depHash
  |>.insert "inputs" self.inputs
  |>.insert "outputs" self.outputs?
  |>.insert "log" self.log
  |>.insert "synthetic" self.synthetic

public instance : ToJson BuildMetadata := ⟨BuildMetadata.toJson⟩

/--
Construct build metadata from a trace stub.
That is, the very old version of the trace file format that just contained a hash.
-/
public def BuildMetadata.ofStub (hash : Hash) : BuildMetadata :=
  {depHash := hash,  inputs := #[], outputs? := none, log := {}, synthetic := false}

public def BuildMetadata.fromJsonObject? (obj : JsonObject) : Except String BuildMetadata := do
  let depHash ←
    if obj.getJson? "schemaVersion" |>.isNone then
      Hash.ofDecimal? (← obj.get "depHash") |>.getDM do
        error "invalid trace: expected string 'depHash' of decimal digits"
    else
      obj.get "depHash"
  let inputs ← obj.getD "inputs" {}
  let outputs? ← obj.getD "outputs" none
  let log ← obj.getD "log" {}
  let synthetic ← obj.getD "synthetic" false
  return {depHash, inputs, outputs?, log, synthetic}

public protected def BuildMetadata.fromJson? (json : Json) : Except String BuildMetadata := do
  match json with
  | .num n =>
    match Hash.ofJsonNumber? n with
    | .ok hash =>
      return .ofStub hash
    | .error reason =>
      error s!"invalid trace stub: {reason}"
  | .obj (o : JsonObject) =>
    match BuildMetadata.fromJsonObject? o with
    | .ok data =>
      return data
    | .error e =>
      if let some (.str ver) := o.getJson? "schemaVersion" then
        if ver == BuildMetadata.schemaVersion then
          error s!"invalid trace: {e}"
      error s!"unknown trace format: {e}"
  | _ =>
    error s!"unknown trace format: expected JSON number or object"

public instance : FromJson BuildMetadata := ⟨BuildMetadata.fromJson?⟩

/-- Parse build metadata from a trace file's contents. -/
public def BuildMetadata.parse (contents : String) : Except String BuildMetadata := do
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
    match Json.parse contents >>= BuildMetadata.fromJson? with
    | .ok data =>
      return .ok data
    | .error e =>
      logWarning s!"{path}: {e}"
      return .invalid
  | .error (.noFileOrDirectory ..) =>
    return .missing
  | .error e =>
    error s!"{path}: read failed: {e}"

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

/-- Indicator of whether a build's output(s) are up-to-date. -/
public inductive OutputStatus
| /-- Needs rebuild -/ outOfDate
| /-- Up-to-date by modification time -/ mtimeUpToDate
| /-- Up-to-date by hash -/ hashUpToDate
deriving DecidableEq

/-- Constructs an `OutputStatus` from a hash check. -/
@[inline] public def OutputStatus.ofHashCheck (upToDate : Bool) : OutputStatus :=
  if upToDate then .hashUpToDate else .outOfDate

/-- Constructs an `OutputStatus` from a modification time check. -/
@[inline] public def OutputStatus.ofMTimeCheck (upToDate : Bool) : OutputStatus :=
  if upToDate then .mtimeUpToDate else .outOfDate

/-- Whether the build should be considered up-to-date for rebuilding. -/
@[inline] public def OutputStatus.isUpToDate (status : OutputStatus) : Bool :=
  status != .outOfDate

/-- Whether the build or rebuild should be considered up-to-date for caching. -/
@[inline] public def OutputStatus.isCacheable (status : OutputStatus) : Bool :=
  status != .mtimeUpToDate

@[specialize] private def checkHashUpToDate'
  [CheckExists ι] [GetMTime ι]
  (info : ι) (depTrace : BuildTrace) (depHash : Option Hash)
  (oldTrace := depTrace.mtime)
: JobM OutputStatus := do
  if depTrace.hash == depHash then
    .ofHashCheck <$> checkExists info
  else if (← getIsOldMode) then
    .ofMTimeCheck <$> oldTrace.checkUpToDate info
  else
    return .outOfDate

/--
Checks if the `info` is up-to-date by comparing `depTrace` with `depHash`.
If old mode is enabled (e.g., `--old`), uses the `oldTrace` modification time
as the point of comparison instead.
-/
@[inline] public def checkHashUpToDate
  [CheckExists ι] [GetMTime ι]
  (info : ι) (depTrace : BuildTrace) (depHash : Option Hash)
  (oldTrace := depTrace.mtime)
: JobM Bool := (·.isUpToDate) <$> checkHashUpToDate' info depTrace depHash oldTrace

/--
Checks whether `info` is up-to-date with the trace.
If so, replays the log of the trace if available.
-/
@[specialize] public def SavedTrace.replayIfUpToDate'
  [CheckExists ι] [GetMTime ι]
  (info : ι) (depTrace : BuildTrace) (savedTrace : SavedTrace)
  (oldTrace := depTrace.mtime)
: JobM OutputStatus := do
  if let .ok data := savedTrace then
    let status ← checkHashUpToDate' info depTrace data.depHash oldTrace
    if status.isUpToDate then
      updateAction .replay
      replay data.log
    return status
  else if (← getIsOldMode) then
    .ofMTimeCheck <$> oldTrace.checkUpToDate info
  else
    return .outOfDate
where replay log := log.replay -- specializes `replay` to `JobM`

/--
Checks whether `info` is up-to-date with the trace.
If so, replays the log of the trace if available.
-/
@[inline] public def SavedTrace.replayIfUpToDate
  [CheckExists ι] [GetMTime ι]
  (info : ι) (depTrace : BuildTrace) (savedTrace : SavedTrace)
  (oldTrace := depTrace.mtime)
: JobM Bool := (·.isUpToDate) <$> savedTrace.replayIfUpToDate' info depTrace oldTrace

/--
Returns if the saved trace exists and its hash matches `inputHash`.

If up-to-date, replays the saved log from the trace and sets the current
build action to `replay`. Otherwise, if the log is empty and trace is synthetic,
or if the trace is not up-to-date, the build action will be set ot `fetch`.
-/
public def SavedTrace.replayOrFetchIfUpToDate (inputHash : Hash) (self : SavedTrace) : JobM Bool := do
  if let .ok data := self then
    if data.depHash == inputHash then
      if data.synthetic && data.log.isEmpty then
        updateAction .fetch
      else
        updateAction .replay
        data.log.replay
      return true
  updateAction .fetch
  return false

/-- **For internal use only.** -/
public class ToOutputJson (α : Type u) where
  toOutputJson (arts : α) : Json

public instance : ToOutputJson PUnit := ⟨fun _ => Json.null⟩
public instance : ToOutputJson Artifact := ⟨(toJson ·.descr)⟩

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
  let noBuildTraceFile := traceFile.addExtension "nobuild"
  if (← getNoBuild) then
    updateAction .build
    writeBuildTrace noBuildTraceFile depTrace Json.null {}
    error s!"target is out-of-date and needs to be rebuilt"
  else
    updateAction action
    let startTime ← IO.monoMsNow
    try
      let iniPos ← getLogPos
      let a ← build -- fatal errors will abort here
      let log := (← getLog).takeFrom iniPos
      writeBuildTrace traceFile depTrace (toOutputJson a) log
      removeFileIfExists noBuildTraceFile
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

**Additional Options:**
* `text`: the contents of `file` are hashed as text rather than as a binary blob.
* `exe`: the cached file will be executable.
* `useLocalFile`: the resulting artifact will use `file`'s path instead of path to
the file in the cache.
-/
public def Cache.saveArtifact
  (cache : Cache) (file : FilePath) (ext := "art") (text exe useLocalFile := false)
: IO Artifact := do
  if text then
    let contents ← IO.FS.readFile file
    let normalized := contents.crlfToLf
    let hash := Hash.ofString normalized
    let descr := artifactWithExt hash ext
    let cacheFile := cache.artifactDir / descr.relPath
    createParentDirs cacheFile
    IO.FS.writeFile cacheFile normalized
    writeFileHash file hash
    let mtime := (← getMTime cacheFile |>.toBaseIO).toOption.getD 0
    let path := if useLocalFile then file else cacheFile
    return {descr, name := file.toString, path, mtime}
  else
    let contents ← IO.FS.readBinFile file
    let hash := Hash.ofByteArray contents
    let descr := artifactWithExt hash ext
    let cacheFile := cache.artifactDir / descr.relPath
    createParentDirs cacheFile
    IO.FS.writeBinFile cacheFile contents
    if exe then
      let r := ⟨true, true, true⟩
      IO.setAccessRights cacheFile ⟨r, r, r⟩ -- 777
    writeFileHash file hash
    let mtime := (← getMTime cacheFile |>.toBaseIO).toOption.getD 0
    let path := if useLocalFile then file else cacheFile
    return {descr, name := file.toString, path, mtime}

@[inline,  inherit_doc Cache.saveArtifact]
public def cacheArtifact
  [MonadWorkspace m] [MonadLiftT IO m] [Monad m]
  (file : FilePath) (ext := "art") (text exe useLocalFile := false)
: m Artifact := do (← getLakeCache).saveArtifact file ext text exe useLocalFile

/-- **For internal use only.** -/
public class ResolveOutputs (m : Type v → Type w) (α : Type v) where
  /-- **For internal use only.** -/
  resolveOutputs? (outputs : Json) : m (Except String α)

open ResolveOutputs in
/--
Retrieve artifacts from the Lake cache using the outputs stored
in either the saved trace file or in the cached input-to-content mapping.

**For internal use only.**
-/
@[specialize] public nonrec def getArtifacts?
  [ResolveOutputs JobM α]
  (inputHash : Hash) (savedTrace : SavedTrace)
  (cache : Cache) (pkg : Package)
: JobM (Option α) := do
  let updateCache ← pkg.isArtifactCacheEnabled
  if let some out ← cache.readOutputs? pkg.cacheScope inputHash then
    match (← resolveOutputs? out) with
    | .ok arts =>
      return some arts
    | .error e =>
      logWarning s!"\
        input '{inputHash.toString.take 7}' found in package artifact cache, \
        but some output(s) have issues: {e}"
  if let .ok data := savedTrace then
    if data.depHash == inputHash then
      if let some out := data.outputs? then
        if let .ok arts ← resolveOutputs? out then
          if updateCache then
            cache.writeOutputs pkg.cacheScope inputHash out
          return some arts
  return none

@[inline] def resolveArtifactOutput?
  [MonadWorkspace m] [MonadLiftT BaseIO m] [Monad m] (output : Json)
: m (Except String Artifact) := do
  match fromJson? output with
  | .ok descr => (← getLakeCache).getArtifact descr |>.toBaseIO
  | .error e => return .error s!"ill-formed artifact output `{output}`: {e}"

instance
  [MonadWorkspace m] [MonadLiftT BaseIO m] [Monad m]
: ResolveOutputs m Artifact := ⟨resolveArtifactOutput?⟩

/--
Construct an artifact from a path outside the Lake artifact cache.

If `text := true`, `file` is hashed as a text file rather than a binary file.
-/
public def computeArtifact (path : FilePath) (ext := "art") (text := false) : JobM Artifact := do
  let hash ← fetchFileHash path text
  let mtime := (← getMTime path |>.toBaseIO).toOption.getD 0
  return {descr := artifactWithExt hash ext, name := path.toString, path, mtime}

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
      let some (art : Artifact) ← getArtifacts? inputHash savedTrace cache pkg
        | return none
      unless (← savedTrace.replayOrFetchIfUpToDate inputHash) do
        removeFileIfExists file
        writeFetchTrace traceFile inputHash (toJson art.descr)
      if restore then
        if !(← file.pathExists) then
          logVerbose s!"restored artifact from cache to: {file}"
          createParentDirs file
          copyFile art.path file
          if exe then
            let r := ⟨true, true, true⟩
            IO.setAccessRights file ⟨r, r, r⟩ -- 777
          writeFileHash file art.hash
        return some (art.useLocalFile file)
      else
        return some art
    let art ← id do
      if (← pkg.isArtifactCacheEnabled) then
        let restore := restore || pkg.restoreAllArtifacts
        if let some art ← fetchArt? restore then
          return art
        else
          let status ← savedTrace.replayIfUpToDate' file depTrace
          unless status.isUpToDate do
            discard <| doBuild depTrace traceFile
          if status.isCacheable then
            let art ← cacheArtifact file ext text exe restore
            cache.writeOutputs pkg.cacheScope inputHash art.descr
            return art
          else
            computeArtifact file ext text
      else if (← savedTrace.replayIfUpToDate file depTrace) then
        computeArtifact file ext text
      else if let some art ← fetchArt? (restore := true) then
        return art
      else
        doBuild depTrace traceFile
    if let some outputsRef := pkg.outputsRef? then
      outputsRef.insert inputHash art.descr
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
      computeArtifact file ext text

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
    let ps ← (← path.walkDir).filterM fun p =>
      -- Always filter out directories as they cannot be hashed anyway
      return !(← p.isDir) && filter p
    -- Makes the order of files consistent across platforms
    let ps := ps.qsort (toString · < toString ·)
    return ps
  job.bindM fun ps =>
    Job.collectArray (traceCaption := path.toString) <$> ps.mapM (inputFile · text)

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
