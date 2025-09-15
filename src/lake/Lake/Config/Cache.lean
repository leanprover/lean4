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
import Lake.Util.Url
import Lake.Util.Proc
import Lake.Util.Reservoir
import Lake.Util.IO

open Lean System

namespace Lake

/--
Maps an input hash to a structure of output artifact content hashes.

These mappings are stored in a per-package JSON Lines file in the Lake cache.
-/
public abbrev CacheMap := Std.HashMap Hash Json

namespace CacheMap

/-- The current version of the input-to-output mappings file format. -/
public def schemaVersion : String := "2025-09-10"

def checkSchemaVersion (inputName : String) (line : String) : LogIO Unit := do
  if line.isEmpty then
    error s!"{inputName}: expected schema version on line 1"
  match Json.parse line >>= fromJson? with
  | .ok (ver : String) =>
      if ver != schemaVersion then
        logWarning s!"{inputName}: unknown schema version '{ver}'; may not parse correctly"
  | .error e =>
    logWarning s!"{inputName}: invalid schema version on line 1: {e}"

/-- Parse a `Cache` from a JSON Lines string. -/
public partial def parse (inputName : String) (contents : String) : LoggerIO CacheMap := do
  let rec loop (i : Nat) (cache : CacheMap) (stopPos pos : String.Pos) := do
    let lfPos := contents.posOfAux '\n' stopPos pos
    let line := contents.extract pos lfPos
    if line.trim.isEmpty then
      return cache
    let cache ← id do
      match Json.parse line >>= fromJson? with
      | .ok (inputHash, arts) =>
        return cache.insert inputHash arts
      | .error e =>
        logWarning s!"{inputName}: invalid JSON on line {i}: {e}"
        return cache
    if h : contents.atEnd lfPos then
      return cache
    else
      loop (i+1) cache stopPos (contents.next' lfPos h)
  let lfPos := contents.posOfAux '\n' contents.endPos 0
  let line := contents.extract 0 lfPos
  checkSchemaVersion inputName line.trim
  if h : contents.atEnd lfPos then
    return {}
  else
    loop 2 {} contents.endPos (contents.next' lfPos h)

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
  let line ← h.getLine
  checkSchemaVersion fileName line
  loop 2 {}

/--
Loads a `CacheMap` from a JSON Lines file.
Errors if the the file is ill-formatted or the read fails for other reasons.
-/
public def load (file : FilePath) : LogIO CacheMap := do
  match (← IO.FS.Handle.mk file .read |>.toBaseIO) with
  | .ok h =>
    h.lock (exclusive := false)
    loadCore h file.toString
  | .error e =>
    error s!"{file}: failed to open file: {e}"

/-
Loads a `CacheMap` from a JSON Lines file. Returns `none` if the file does not exist.
Errors if the manifest is ill-formatted or the read fails for other reasons.
-/
public def load? (file : FilePath) : LogIO (Option CacheMap) := do
  match (← IO.FS.Handle.mk file .read |>.toBaseIO) with
  | .ok h =>
    h.lock (exclusive := false)
    loadCore h file.toString
  | .error (.noFileOrDirectory ..) =>
    return none
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
    h.putStrLn (toJson schemaVersion).compress
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

/-- Extract each output from their structured data into a flat array of artifact descriptions. -/
public partial def collectOutputDescrs (map : CacheMap) : LogIO (Array ArtifactDescr) := do
  throwIfLogs <| map.foldM (init := #[]) fun as _ o => go as o
where go as o := do
  match o with
  | .null =>
    return as
  | .bool b =>
    logError s!"unsupported output: {b}"
    return as
  | .num o =>
    match Hash.ofJsonNumber? o with
    | .ok hash =>
      return as.push {hash}
    | .error reason =>
      logError s!"unsupported output; {reason}: {o}"
      return as
  | .str o =>
    match ArtifactDescr.ofFilePath? o with
    | .ok a => return as.push a
    | .error e =>
      logError s!"unsupported output: {e}"
      return as
  | .arr os => os.foldlM (init := as) go
  | .obj os => os.foldlM (init := as) fun as _ o => go as o

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
@[inline] public protected def artifactPath (cache : Cache) (contentHash : Hash) (ext := "art")  : FilePath :=
  cache.artifactDir / artifactPath contentHash ext

/-- Returns the artifact in the Lake cache corresponding the given artifact description. -/
public def getArtifact? (cache : Cache) (descr : ArtifactDescr) : BaseIO (Option Artifact) := do
  let path := cache.artifactDir / descr.toFilePath
  if let .ok mtime ← getMTime path |>.toBaseIO then
    return some {descr, path, mtime}
  else if (← path.pathExists) then
    return some {descr, path, mtime := 0}
  else
    return none

/-- Returns path to the artifact for each output. Errors if any are missing. -/
public def getArtifactPaths
  (cache : Cache) (descrs : Array ArtifactDescr)
: LogIO (Vector FilePath descrs.size) := throwIfLogs do
  (Vector.mk descrs rfl).mapM fun out => do
    let art := cache.artifactDir / out.toFilePath
    unless (← art.pathExists) do
      logError s!"artifact not found in cache: {art}"
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
public def readOutputs? (cache : Cache) (scope : String) (inputHash : Hash) : LogIO (Option Json) := do
  let path := cache.outputsFile scope inputHash
  match (← IO.FS.readFile path |>.toBaseIO) with
  | .ok contents =>
    match Json.parse contents with
    | .ok outputs => return outputs
    | .error e =>
      logWarning s!"{path}: invalid JSON: {e}"
      return none
  | .error (.noFileOrDirectory ..) => return none
  | .error e => error s!"{path}: read failed: {e}"

/-- The directory where input-to-output mappings of downloaded package revisions are cached. -/
@[inline] public def revisionDir (cache : Cache) : FilePath :=
  cache.dir / "revisions"

/-- Returns path to the input-to-output mappings of a downloaded package revision. -/
@[inline] public def revisionPath (cache : Cache) (scope : String) (rev : String)   : FilePath :=
  cache.revisionDir / scope / s!"{rev}.jsonl"

end Cache

/-- Uploads a file to an online bucket using the Amazon S3 protocol. -/
def uploadS3
  (file : FilePath) (contentType : String) (url : String) (key : String)
: LoggerIO Unit := do
  proc {
    cmd := "curl"
    args := #[
      "-s",
      "--aws-sigv4", "aws:amz:auto:s3", "--user", key,
      "-X", "PUT", "-T", file.toString, url,
      "-H",  s!"Content-Type: {contentType}"
    ]
  } (quiet := true)

/--
Configuration of a remote cache service (e.g., Reservoir or an S3 bucket).

All fields are not required to be valid.
A user should set at least the necessary ones for a given function.
-/
public structure CacheService where
  key : String := ""
  artifactEndpoint : String := ""
  revisionEndpoint : String := ""
  /-- Reservoir API endpoint. -/
  apiEndpoint? : Option String := none

namespace CacheService

/-- The MIME type of Lake/Reservoir artifact. -/
public def artifactContentType : String := "application/vnd.reservoir.artifact"

public def artifactUrl (contentHash : Hash) (scope : String) (service : CacheService) : String :=
  let scope := "/".intercalate <| scope.split (· == '/') |>.map uriEncode
  if let some apiEndpoint := service.apiEndpoint? then
    s!"{apiEndpoint}/packages/{scope}/artifacts/{contentHash.hex}.art"
  else
    s!"{service.artifactEndpoint}/{scope}/{contentHash.hex}.art"

public def downloadArtifact
  (descr : ArtifactDescr) (cache : Cache) (scope : String)
  (service : CacheService) (force := false)
: LoggerIO Unit := do
  let url := service.artifactUrl descr.hash scope
  let path := cache.artifactDir / descr.toFilePath
  if (← path.pathExists) && !force then
    return
  logInfo s!"\
    {scope}: downloading artifact {descr.hash}\
    \n  local path: {path}\
    \n  remote URL: {url}"
  download url path
  let hash ← computeFileHash path
  if hash != descr.hash then
    logError s!"{path}: downloaded artifact does not have expect hash"
    IO.FS.removeFile path
    failure

public def downloadArtifacts
   (descrs : Array ArtifactDescr) (cache : Cache) (scope : String)
   (service : CacheService) (force := false)
: LoggerIO Unit := do
  let ok ← descrs.foldlM (init := true) fun ok descr =>
    try
      service.downloadArtifact descr cache scope force
      return ok
    catch _ =>
      return false
  unless ok do
    error s!"{scope}: failed to download some artifacts"

public def downloadOutputArtifacts
  (map : CacheMap) (cache : Cache) (remoteScope localScope : String)
  (service : CacheService) (force := false)
: LoggerIO Unit := do
  cache.writeMap localScope map
  let descrs ← map.collectOutputDescrs
  service.downloadArtifacts descrs cache remoteScope force

public def uploadArtifact
  (contentHash : Hash) (art : FilePath) (scope : String) (service : CacheService)
: LoggerIO Unit := do
  let url := service.artifactUrl contentHash scope
  logInfo s!"\
    {scope}: uploading artifact {contentHash}\
    \n  local path: {art}\
    \n  remote URL: {url}"
  uploadS3 art artifactContentType url service.key

public def uploadArtifacts
  (descrs : Vector ArtifactDescr n) (paths : Vector FilePath n) (scope : String)  (service : CacheService)
: LoggerIO Unit := n.forM fun n h => uploadArtifact descrs[n].hash paths[n] scope service

/-- The MIME type of Lake/Reservoir input-to-output mappings for a Git revision. -/
public def mapContentType : String := "application/vnd.reservoir.outputs+json-lines"

public def revisionUrl (rev : String) (scope : String) (service : CacheService) :=
  let scope := "/".intercalate <| scope.split (· == '/') |>.map uriEncode
 if let some apiEndpoint := service.apiEndpoint? then
    s!"{apiEndpoint}/packages/{scope}/revisions/{rev}/outputs.jsonl"
  else
    s!"{service.revisionEndpoint}/{scope}/{rev}.jsonl"

public def downloadRevisionOutputs?
  (rev : String) (cache : Cache) (scope : String)
  (service : CacheService) (force := false)
: LoggerIO (Option CacheMap) := do
  let path := cache.revisionPath rev scope
  if (← path.pathExists) && !force then
    return ← CacheMap.load path
  let url := service.revisionUrl rev scope
  logInfo s!"\
    {scope}: downloading build outputs for revision {rev}\
    \n  local path: {path}\
    \n  remote URL: {url}"
  let headers := if service.apiEndpoint?.isSome then Reservoir.lakeHeaders else {}
  let contents? ← try getUrl? url headers catch e =>
    logError s!"{scope}: output lookup failed"
    throw e
  let some contents := contents?
    | return none
  createParentDirs path
  IO.FS.writeFile path contents
  CacheMap.load path

public def uploadRevisionOutputs
  (rev : String) (outputs : FilePath) (scope : String) (service : CacheService)
: LoggerIO Unit := do
  let url := service.revisionUrl rev scope
  logInfo s!"\
    {scope}: uploading build outputs for revision {rev}\
    \n  local path: {outputs}\
    \n  remote URL: {url}"
  uploadS3 outputs mapContentType url service.key

end CacheService
