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
import Lake.Build.Actions
import Lake.Util.Proc
import Lake.Util.Url
import Lake.Util.IO

open Lean System

namespace Lake

/--
Maps an input hash to a structure of output artifact content hashes.

These mappings are stored in a per-package JSON Lines file in the Lake cache.
-/
public abbrev CacheMap := Std.HashMap Hash Json

namespace CacheMap

/-- Parse a `Cache` from a JSON Lines string. -/
public partial def parse (contents : String) : LogIO CacheMap := do
  let rec loop (i : Nat) (cache : CacheMap) (stopPos pos : String.Pos) := do
    let endPos := contents.posOfAux '\n' stopPos pos
    if h : contents.atEnd endPos then
      return cache
    else
      let line := contents.extract pos endPos
      match Json.parse line >>= fromJson? with
      | .ok (inputHash, arts) =>
        loop (i+1) (cache.insert inputHash arts) stopPos (contents.next' endPos h)
      | .error e =>
        logWarning s!"invalid JSON on line {i}: {e}"
        loop (i+1) cache stopPos (contents.next' endPos h)
  loop 1 {} contents.endPos 0

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

/-- Extract each output hash from their structured data into a flat array. -/
public partial def collectOutputHashes (map : CacheMap) : LogIO (Array Hash) := do
  throwIfLogs <| map.foldM (init := #[]) fun as _ o => go as o
where go as o := do
  match o with
  | .num o =>
    if o.exponent = 0 && 0 < o.mantissa then
      if h : o.mantissa.toNat < UInt64.size then
        return as.push ⟨.ofNatLT o.mantissa.toNat h⟩
      else
        logError s!"unsupported output; decimal too big: {o}"
        return as
    else
      logError s!"unsupported output; number is not a natural: {o}"
      return as
  | .str o =>
    if let some hash := Hash.ofDecimal? o then
      return as.push hash
    else
      logError s!"unsupported output; invalid hash string: {o}"
      return as
  | .arr os => os.foldlM (init := as) go
  | .obj os => os.foldlM (init := as) fun as _ o => go as o
  | o =>
    logError s!"unsupported output: {o.pretty}"
    return as

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

/-- Returns the path to the artifact in the Lake cache with extension `ext` if it exists. -/
public def getArtifact? (cache : Cache) (contentHash : Hash) (ext := "art")  : BaseIO (Option Artifact) := do
  let path := cache.artifactPath contentHash ext
  if let .ok mtime ← getMTime path |>.toBaseIO then
    return some {path, mtime, hash := contentHash}
  else if (← path.pathExists) then
    return some {path, mtime := 0, hash := contentHash}
  else
    return none

/-- Returns path to the artifact for each hash. Errors if any are missing. -/
public def getArtifacts
  (cache : Cache) (hashes : Array Hash)
: LogIO (Vector FilePath hashes.size) := throwIfLogs do
  (Vector.mk hashes rfl).mapM fun hash => do
    let art := cache.artifactPath hash
    unless (← art.pathExists) do
      logError s!"artifact for output {hash} not found in the cache"
    return art

/-- The directory where input-to-output mappings are stored in the Lake cache. -/
@[inline] public def outputsDir (cache : Cache) : FilePath :=
  cache.dir / "outputs"

/-- The file containing the outputs of the the given input for the package. -/
@[inline] public def outputsFile (cache : Cache) (scope : String) (inputHash : Hash) : FilePath  :=
  cache.outputsDir / scope / s!"{inputHash}.json"

/-- Cache the outputs corresponding to the given input for the package.  -/
public def writeOutputsCore
  (cache : Cache) (scope : String) (inputHash : Hash) (outputs : Json)
: IO Unit := do
  let file := cache.outputsFile scope inputHash
  createParentDirs file
  IO.FS.writeFile file outputs.compress

/-- Cache the outputs corresponding to the given input for the package.  -/
@[inline] public def writeOutputs
  [ToJson α] (cache : Cache) (scope : String) (inputHash : Hash) (outputs : α)
: IO Unit := cache.writeOutputsCore scope inputHash (toJson outputs)

/-- Cache the input-to-outputs mappings from a `CacheMap`.  -/
public def writeMap (cache : Cache) (scope : String) (map : CacheMap) : IO Unit :=
  map.forM fun i o => cache.writeOutputsCore scope i o

/-- Retrieve the cached outputs corresponding to the given input for the package (if any). -/
public def readOutputs? (cache : Cache) (scope : String) (inputHash : Hash) : IO (Option Json) := do
  let path := cache.outputsFile scope inputHash
  match (← IO.FS.readFile path |>.toBaseIO) with
  | .ok contents =>
    match Json.parse contents with
    | .ok outputs => return outputs
    | .error e => throw <| IO.userError s!"{path}: invalid JSON: {e}"
  | .error (.noFileOrDirectory ..) => return none
  | .error e => throw e

end Cache

/-- Uploads a file to an online bucket using the Amazon S3 protocol. -/
def uploadS3
  (file : FilePath) (contentType : String) (url : String) (key : String)
: LogIO Unit := do
  logInfo s!"uploading {file} to {url}"
  proc {
    cmd := "curl"
    args := #[
      "--aws-sigv4", "aws:amz:auto:s3", "--user", key,
      "-X", "PUT", "-T", file.toString, url,
      "-H",  s!"Content-Type: {contentType}"
    ]
  }

/--
Cache service description.

Fields may be missing (be the empty string).
Necessary fields are assumed to have been set by the producer for the consumer.
-/
public structure CacheService where
  key : String := ""
  artEndpoint : String := ""
  revEndpoint : String := ""

namespace CacheService

/-- The MIME type of Lake/Reservoir artifact. -/
public def artifactContentType : String := "application/vnd.reservoir.artifact"

public def artifactUrl (contentHash : Hash) (scope : String) (service : CacheService) (ext := "art") :=
  s!"{service.artEndpoint}/{uriEncode scope}/{contentHash}.{ext}"

public def downloadArtifact
  (cache : Cache) (contentHash : Hash) (scope : String) (service : CacheService) (ext := "art")
: LogIO Unit :=
  let url := service.artifactUrl contentHash scope ext
  let path := cache.artifactPath contentHash ext
  download url path

public def downloadArtifacts
  (cache : Cache) (contentHashes : Array Hash) (scope : String) (service : CacheService)
: LogIO Unit := do
  contentHashes.forM fun hash => downloadArtifact cache hash scope service

public def uploadArtifact
  (contentHash : Hash) (art : FilePath) (scope : String) (service : CacheService)
: LogIO Unit :=
  let url := service.artifactUrl contentHash scope
  uploadS3 art artifactContentType url service.key

public def uploadArtifacts
  (hashes : Vector Hash n) (arts : Vector FilePath n) (scope : String)  (service : CacheService)
: LogIO Unit := n.forM fun n h => uploadArtifact hashes[n] arts[n] scope service

/-- The MIME type of Lake/Reservoir input-to-output mappings for a Git revision. -/
public def mapContentType : String := "application/vnd.reservoir.outputs+json-lines"

public def revisionUrl (rev : String) (scope : String) (service : CacheService) :=
  s!"{service.revEndpoint}/{uriEncode scope}/{rev}.jsonl"

public def downloadRevisionOutputs (rev : String) (scope : String) (service : CacheService) : LogIO CacheMap := do
  let url := service.revisionUrl rev scope
  let r ← try getUrl url catch e =>
    logError s!"{scope}: revision {rev} not found at endpoint"
    throw e
  CacheMap.parse r

public def uploadRevisionOutputs
  (rev : String) (outputs : FilePath) (scope : String) (service : CacheService)
: LogIO Unit := uploadS3 outputs mapContentType (service.revisionUrl rev scope) service.key

end CacheService
