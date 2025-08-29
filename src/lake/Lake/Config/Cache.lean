/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Util.Log
public import Lake.Config.Artifact
public import Lake.Build.Trace
import Lake.Util.IO

open Lean System

namespace Lake

/-- The Lake cache directory. -/
public structure Cache where
  dir : FilePath
  deriving Inhabited

namespace Cache

/-- Returns the artifact directory for the Lake cache. -/
@[inline] public def artifactDir (cache : Cache) : FilePath :=
  cache.dir / "artifacts"

/-- Returns the path to artifact in the Lake cache with extension `ext`. -/
public def artifactPath (cache : Cache) (contentHash : Hash) (ext := "art")  : FilePath :=
  cache.artifactDir / if ext.isEmpty then contentHash.toString else s!"{contentHash}.{ext}"

/--
Returns the path to the artifact in the Lake cache with extension `ext` if it exists. -/
public def getArtifact? (cache : Cache) (contentHash : Hash) (ext := "art")  : BaseIO (Option Artifact) := do
  let path := cache.artifactPath contentHash ext
  if let .ok mtime ← getMTime path |>.toBaseIO then
    return some {path, mtime, hash := contentHash}
  else if (← path.pathExists) then
    return some {path, mtime := 0, hash := contentHash}
  else
    return none

/-- The directory where input-to-output mappings are stored in the Lake cache. -/
@[inline] public def outputsDir (cache : Cache) : FilePath :=
  cache.dir / "outputs"

/-- The file containing the outputs of the the given input for the package. -/
@[inline] public def outputsFile (cache : Cache) (pkg : String) (inputHash : Hash) : FilePath  :=
  cache.outputsDir / pkg / s!"{inputHash}.json"

/-- Cache the outputs corresponding to the given input for the package.  -/
public def writeOutputsCore
  (cache : Cache) (pkg : String) (inputHash : Hash) (outputs : Json)
: IO Unit := do
  let file := cache.outputsFile pkg inputHash
  createParentDirs file
  IO.FS.writeFile file outputs.compress

/-- Cache the outputs corresponding to the given input for the package.  -/
@[inline] public def writeOutputs
  [ToJson α] (cache : Cache) (pkg : String) (inputHash : Hash) (outputs : α)
: IO Unit := cache.writeOutputsCore pkg inputHash (toJson outputs)

/-- Retrieve the cached outputs corresponding to the given input for the package (if any). -/
public def readOutputs? (cache : Cache) (pkg : String) (inputHash : Hash) : IO (Option Json) := do
  let path := cache.outputsFile pkg inputHash
  match (← IO.FS.readFile path |>.toBaseIO) with
  | .ok contents =>
    match Json.parse contents with
    | .ok outputs => return outputs
    | .error e => throw <| IO.userError s!"{path}: invalid JSON: {e}"
  | .error (.noFileOrDirectory ..) => return none
  | .error e => throw e

end Cache

/--
Maps an input hash to a structure of output artifact content hashes.

These mappings are stored in a per-package JSON Lines file in the Lake cache.
-/
public abbrev CacheMap := Std.HashMap Hash Json

namespace CacheMap

@[inline] private partial def loadCore
  (h : IO.FS.Handle) (fileName : String)
: LogIO CacheMap := do
  let rec loop (i : Nat) (cache : CacheMap) := do
    let line ← h.getLine
    if line.isEmpty then
      return cache
    match Json.parse line >>= fromJson? with
    | .ok (inputHash, arts) =>
      loop (i+1) (cache.insert inputHash arts)
    | .error e =>
      logWarning s!"{fileName}: invalid JSON on line {i}: {e}"
      loop (i+1) cache
  loop 1 {}

/-- Load a `CacheMap` from a JSON Lines file. -/
public def load (file : FilePath) : LogIO CacheMap := do
  match (← IO.FS.Handle.mk file .read |>.toBaseIO) with
  | .ok h =>
    h.lock (exclusive := false)
    loadCore h file.toString
  | .error (.noFileOrDirectory ..) =>
    return {}
  | .error e =>
    error s!"{file}: failed to open file: {e}"

/--
Save a `CacheMap` to a JSON Lines file.
Entries already in the file but not in the map will not be removed.
-/
public def updateFile (file : FilePath) (cache : CacheMap) : LogIO Unit := do
  createParentDirs file
  discard <| IO.FS.Handle.mk file .append -- ensure file exists
  match (← IO.FS.Handle.mk file .readWrite |>.toBaseIO) with
  | .ok h =>
    h.lock (exclusive := true)
    let currEntries ← loadCore h file.toString
    let cache := cache.fold (fun m k v => m.insert k v) currEntries
    h.rewind
    cache.forM fun k v =>
       h.putStrLn (toJson (k, v)).compress
  | .error e =>
    error s!"{file}: failed to open file: {e}"

/-- Write a `CacheMap` to a JSON Lines file. -/
public def writeFile (file : FilePath) (cache : CacheMap) : LogIO Unit := do
  createParentDirs file
  match (← IO.FS.Handle.mk file .write |>.toBaseIO) with
  | .ok h =>
    h.lock (exclusive := true)
    cache.forM fun k v =>
       h.putStrLn (toJson (k, v)).compress
  | .error e =>
    error s!"{file}: failed to open file: {e}"

/-- Returns the output data associated with the input hash in the cache. -/
public nonrec def get? (inputHash : Hash) (cache : CacheMap) : Option Json :=
  cache.get? inputHash

/-- Associate output data (as JSON) with the given the input hash. -/
public def insertCore (inputHash : Hash) (val : Json) (cache : CacheMap) : CacheMap :=
  cache.insert inputHash val

/-- Associate output data with the given the input hash. -/
@[inline] public def insert [ToJson α] (inputHash : Hash) (val : α) (cache : CacheMap) : CacheMap :=
  cache.insertCore inputHash (toJson val)

end CacheMap

/-- A mutable reference to a `CacheMap`. -/
public abbrev CacheRef := IO.Ref CacheMap

namespace CacheRef

@[inline] public def mk (init : CacheMap := {}) : BaseIO CacheRef :=
  IO.mkRef init

@[inline, inherit_doc CacheMap.get?]
public def get? (inputHash : Hash) (cache : CacheRef) : BaseIO (Option Json) :=
  cache.modifyGet fun m => (m.get? inputHash, m)

@[inline, inherit_doc CacheMap.insert]
public def insert [ToJson α] (inputHash : Hash) (val : α) (cache : CacheRef) : BaseIO Unit :=
  cache.modify (·.insert inputHash (toJson val))

end CacheRef
