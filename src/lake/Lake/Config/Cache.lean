/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Util.Log
public import Lake.Config.Artifact
import Lake.Config.InstallPath
import Lake.Build.Actions
import Lake.Util.Url
import Lake.Util.Proc
import Lake.Util.Reservoir
import Lake.Util.JsonObject
import Lake.Util.IO
import Init.Data.String.Lemmas

open Lean System

namespace Lake

/-! ## Cache Map -/

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
  let rec loop (i : Nat) (cache : CacheMap) {contents : String} (pos : contents.Pos) := do
    let lfPos := pos.find '\n'
    let line := contents.slice pos lfPos (by simp [lfPos])
    if line.trimAscii.isEmpty then
      return cache
    let cache ← id do
      match Json.parse line.copy >>= fromJson? with
      | .ok (inputHash, arts) =>
        return cache.insert inputHash arts
      | .error e =>
        logWarning s!"{inputName}: invalid JSON on line {i}: {e}"
        return cache
    if h : lfPos.IsAtEnd then
      return cache
    else
      loop (i+1) cache (lfPos.next h)
  let lfPos := contents.find '\n'
  let line := contents.sliceTo lfPos
  checkSchemaVersion inputName line.trimAscii.copy
  if h : lfPos.IsAtEnd then
    return {}
  else
    loop 2 {} (lfPos.next h)

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
Errors if the file is ill-formatted or the read fails for other reasons.
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

/-! ## Cache Ref -/

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

/-! ## Local Cache -/

/-- The Lake cache directory. -/
public structure Cache where
  dir : FilePath
  deriving Inhabited

/-- The current version of the output file format. -/
def CacheOutput.schemaVersion : String := "2026-01-22"

structure CacheOutput where
  service? : Option String := none
  data : Json
  deriving ToJson

namespace CacheOutput

protected def toJson (out : CacheOutput) : Json :=
  JsonObject.empty
  |>.insert "schemaVersion" schemaVersion
  |>.insert "service" out.service?
  |>.insert "data" out.data

instance : ToJson CacheOutput := ⟨CacheOutput.toJson⟩

protected def fromJson? (json : Json) : Except String CacheOutput := do
  if let .obj obj := json then
    let obj := JsonObject.mk obj
    if obj.contains "schemaVersion" then
      -- presumably the new format
      -- (the edge case of a custom output with a `schemaVersion` is not worth covering)
      let service? ← obj.get? "service"
      let data ← obj.get "data"
      return {service?, data}
    else
      -- old format: just the data
      return {data := json}
  else
    -- old format: just the data
    return {data := json}

instance : FromJson CacheOutput := ⟨CacheOutput.fromJson?⟩

end CacheOutput

namespace Cache

/-- Returns the artifact directory for the Lake cache. -/
@[inline] public def artifactDir (cache : Cache) : FilePath :=
  cache.dir / "artifacts"

/-- Returns the path to artifact in the Lake cache with extension `ext`. -/
@[inline] public protected def artifactPath (cache : Cache) (contentHash : Hash) (ext := "art")  : FilePath :=
  cache.artifactDir / artifactPath contentHash ext

/-- Returns the artifact in the Lake cache corresponding the given artifact description. -/
public def getArtifact? (cache : Cache) (descr : ArtifactDescr) : BaseIO (Option Artifact) := do
  let path := cache.artifactDir / descr.relPath
  if let .ok mtime ← getMTime path |>.toBaseIO then
    return some {descr, path, mtime}
  else if (← path.pathExists) then
    return some {descr, path, mtime := 0}
  else
    return none

/-- Returns the artifact in the Lake cache corresponding the given artifact description. Errors if missing. -/
public def getArtifact (cache : Cache) (descr : ArtifactDescr) : EIO String Artifact := do
  let path := cache.artifactDir / descr.relPath
  if let .ok mtime ← getMTime path |>.toBaseIO then
    return {descr, path, mtime}
  else if (← path.pathExists) then
    return {descr, path, mtime := 0}
  else
    error s!"artifact not found in cache: {path}"

/-- Returns path to the artifact for each output. Errors if any are missing. -/
public def getArtifactPaths
  (cache : Cache) (descrs : Array ArtifactDescr)
: LogIO (Vector FilePath descrs.size) := throwIfLogs do
  (Vector.mk descrs rfl).mapM fun out => do
    let art := cache.artifactDir / out.relPath
    unless (← art.pathExists) do
      logError s!"artifact not found in cache: {art}"
    return art

/-- The directory where input-to-output mappings are stored in the Lake cache. -/
@[inline] public def outputsDir (cache : Cache) : FilePath :=
  cache.dir / "outputs"

/-- The file containing the outputs of the given input for the package. -/
@[inline] public def outputsFile (cache : Cache) (scope : String) (inputHash : Hash) : FilePath  :=
  cache.outputsDir / scope / s!"{inputHash}.json"

/-- Cache the outputs corresponding to the given input for the package.  -/
def writeOutputsCore
  (cache : Cache) (scope : String) (inputHash : Hash) (outputs : Json)
  (service? : Option String := none)
: IO Unit := do
  let file := cache.outputsFile scope inputHash
  createParentDirs file
  let out:= {service?, data := outputs : CacheOutput}
  IO.FS.writeFile file (toJson out).compress

/-- Cache the outputs corresponding to the given input for the package.  -/
@[inline] public def writeOutputs
  [ToJson α] (cache : Cache) (scope : String) (inputHash : Hash) (outputs : α)
  (service? : Option String := none)
: IO Unit := cache.writeOutputsCore scope inputHash (toJson outputs) service?

/-- Cache the input-to-outputs mappings from a `CacheMap`.  -/
public def writeMap
  (cache : Cache) (scope : String) (map : CacheMap) (service? : Option String := none)
: IO Unit := map.forM fun i o => cache.writeOutputsCore scope i o service?

/-- Retrieve the cached outputs corresponding to the given input for the package (if any). -/
public def readOutputs? (cache : Cache) (scope : String) (inputHash : Hash) : LogIO (Option Json) := do
  let path := cache.outputsFile scope inputHash
  match (← IO.FS.readFile path |>.toBaseIO) with
  | .ok contents =>
    match Json.parse contents >>= fromJson? with
    | .ok out =>
      return CacheOutput.data out
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

/-! ## Remote Cache Service -/

/-- Uploads a file to an online bucket using the Amazon S3 protocol. -/
def uploadS3
  (file : FilePath) (contentType : String) (url : String) (key : String)
: LoggerIO Unit := do
  let out ← captureProc' {
    cmd := "curl"
    args := #[
      "-s", "-w", "%{stderr}%{json}\n",
      "--aws-sigv4", "aws:amz:auto:s3", "--user", key,
      "-X", "PUT", "-T", file.toString, url,
      "-H",  s!"Content-Type: {contentType}"
    ]
  }
  match Json.parse out.stderr >>= JsonObject.fromJson? with
  | .ok data =>
    let code ← id do
      match (data.get? "response_code" <|> data.get? "http_code") with
      | .ok (some code) => return code
      | .ok none => error s!"curl's JSON output did not contain a response code"
      | .error e => error s!"curl's JSON output contained an invalid JSON response code: {e}"
    unless code == 200 do
      error s!"failed to upload artifact, error {code}; received:\n{out.stdout}"
  | .error e =>
    error s!"curl produced invalid JSON output: {e}"

/--
Configuration of a remote cache service (e.g., Reservoir or an S3 bucket).

A given configuration is not required to support all cache service functions, and no validation
of the configuration is performed by its operations. Users should construct a service that supports
the desired functions by using `CacheService`'s smart constructors
(e.g., `reservoir`, `uploadService`).
-/
public structure CacheService where
  private mk ::
    private name? : Option String := none
    /- S3 Bucket -/
    private key : String := ""
    private artifactEndpoint : String := ""
    private revisionEndpoint : String := ""
    /- Reservoir -/
    /-- Is this a Reservoir cache service configuration? -/
    isReservoir : Bool := false
    private apiEndpoint : String := ""
    /--  Whether interpret the scope as a repository or not. -/
    private repoScope : Bool := false

namespace CacheService

/-! ### Constructors -/

/-- Constructs a `CacheService` for a Reservoir endpoint. -/
@[inline] public def reservoirService (apiEndpoint : String) (repoScope := false) : CacheService :=
  {name? := some "reservoir", isReservoir := true, apiEndpoint, repoScope}

/-- Constructs a `CacheService` to upload artifacts and/or outputs to an S3 endpoint. -/
@[inline] public def uploadService
  (key artifactEndpoint revisionEndpoint : String)
: CacheService := {key, artifactEndpoint, revisionEndpoint}

/-- Constructs a `CacheService` to download artifacts and/or outputs from to an S3 endpoint. -/
@[inline] public def downloadService
  (artifactEndpoint revisionEndpoint : String) (name? : Option String := none)
: CacheService := {name?, artifactEndpoint, revisionEndpoint}

/-- Constructs a `CacheService` to download just artifacts from to an S3 endpoint. -/
@[inline] public def downloadArtsService
  (artifactEndpoint : String) (name? : Option String := none)
: CacheService := {name?, artifactEndpoint}

/--
Reconfigures the cache service to interpret scopes as repositories (or not if `false`).

For custom endpoints, if `true`, Lake will augment the provided scope with
toolchain and platform information in a manner similar to Reservoir.
-/
@[inline] public def withRepoScope (service : CacheService) (repoScope := true) : CacheService :=
  {service with repoScope}

/-! ### Artifact Transfer -/

/-- The MIME type of Lake/Reservoir artifact. -/
public def artifactContentType : String := "application/vnd.reservoir.artifact"

private def appendScope (endpoint : String) (scope : String) : String :=
  scope.split '/' |>.fold (init := endpoint) fun s component =>
    uriEncode component.copy s |>.push '/'

private def s3ArtifactUrl (contentHash : Hash) (service : CacheService) (scope : String) : String :=
  appendScope s!"{service.artifactEndpoint}/" scope ++ s!"{contentHash.hex}.art"

public def artifactUrl (contentHash : Hash) (service : CacheService) (scope : String) : String :=
  if service.isReservoir then
    let endpoint :=
      if service.repoScope then
        s!"{service.apiEndpoint}/repositories/"
      else
        s!"{service.apiEndpoint}/packages/"
    appendScope endpoint scope ++ s!"artifacts/{contentHash.hex}.art"
  else
    service.s3ArtifactUrl contentHash scope

public def downloadArtifact
  (descr : ArtifactDescr) (cache : Cache)
  (service : CacheService) (scope : String) (force := false)
: LoggerIO Unit := do
  let url := service.artifactUrl descr.hash scope
  let path := cache.artifactDir / descr.relPath
  if (← path.pathExists) && !force then
    return
  logInfo s!"\
    {scope}: downloading artifact {descr.hash}\
    \n  local path: {path}\
    \n  remote URL: {url}"
  download url path
  let hash ← computeFileHash path
  if hash != descr.hash then
    logError s!"{path}: downloaded artifact does not have the expected hash"
    IO.FS.removeFile path
    failure

public def downloadArtifacts
   (descrs : Array ArtifactDescr) (cache : Cache)
   (service : CacheService) (scope : String) (force := false)
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
  (map : CacheMap) (cache : Cache) (service : CacheService)
  (localScope remoteScope : String) (force := false)
: LoggerIO Unit := do
  cache.writeMap localScope map service.name?
  let descrs ← map.collectOutputDescrs
  service.downloadArtifacts descrs cache remoteScope force

public def uploadArtifact
  (contentHash : Hash) (art : FilePath) (service : CacheService) (scope : String)
: LoggerIO Unit := do
  let url := service.s3ArtifactUrl contentHash scope
  logInfo s!"\
    {scope}: uploading artifact {contentHash}\
    \n  local path: {art}\
    \n  remote URL: {url}"
  uploadS3 art artifactContentType url service.key

public def uploadArtifacts
  (descrs : Vector ArtifactDescr n) (paths : Vector FilePath n)
  (service : CacheService) (scope : String)
: LoggerIO Unit := n.forM fun n h => service.uploadArtifact descrs[n].hash paths[n] scope

/-! ### Output Transfer -/

/-- The MIME type of Lake/Reservoir input-to-output mappings for a Git revision. -/
public def mapContentType : String := "application/vnd.reservoir.outputs+json-lines"

private def s3RevisionUrl
  (rev : String) (service : CacheService) (scope : String)
  (platform : String := "") (toolchain : String := "")
: String := Id.run do
  let mut url := appendScope s!"{service.revisionEndpoint}/" scope
  if service.repoScope then
    unless platform.isEmpty do
      url := uriEncode platform s!"{url}pt/" |>.push '/'
    unless toolchain.isEmpty do
      url := uriEncode (toolchain2Dir toolchain).toString s!"{url}tc/" |>.push '/'
  return s!"{url}{rev}.jsonl"

public def revisionUrl
  (rev : String) (service : CacheService) (scope : String)
  (platform : String := "") (toolchain : String := "")
: String :=
  if service.isReservoir then Id.run do
    let mut url := service.apiEndpoint
    if service.repoScope then
      url := url ++ "/repositories/"
    else
      url := url ++ "/packages/"
    url := appendScope url scope ++ s!"build-outputs?rev={rev}"
    unless platform.isEmpty do
      url := uriEncode platform s!"{url}&platform="
    unless toolchain.isEmpty do
      url := uriEncode toolchain s!"{url}&toolchain="
    return url
  else
    service.s3RevisionUrl rev scope platform toolchain

public def downloadRevisionOutputs?
  (rev : String) (cache : Cache) (service : CacheService) (localScope remoteScope : String)
  (platform : String := "") (toolchain : String := "") (force := false)
: LoggerIO (Option CacheMap) := do
  -- TODO: toolchain-scoped revision paths for system cache?
  let path := cache.revisionPath localScope rev
  if (← path.pathExists) && !force then
    return ← CacheMap.load path
  let url := service.revisionUrl rev remoteScope platform toolchain
  logInfo s!"\
    {localScope}: downloading build outputs for revision {rev}\
    \n  local path: {path}\
    \n  remote URL: {url}"
  let headers := if service.isReservoir then Reservoir.lakeHeaders else {}
  let contents? ← try getUrl? url headers catch e =>
    logError s!"{remoteScope}: output lookup failed"
    throw e
  let some contents := contents?
    | return none
  createParentDirs path
  IO.FS.writeFile path contents
  CacheMap.load path

public def uploadRevisionOutputs
  (rev : String) (outputs : FilePath) (service : CacheService) (scope : String)
  (platform : String := "") (toolchain : String := "")
: LoggerIO Unit := do
  let url := service.s3RevisionUrl rev scope platform toolchain
  logInfo s!"\
    {scope}: uploading build outputs for revision {rev}\
    \n  local path: {outputs}\
    \n  remote URL: {url}"
  uploadS3 outputs mapContentType url service.key

end CacheService
