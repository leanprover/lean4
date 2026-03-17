/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
import Init.Control.Do
public import Lake.Util.Log
public import Lake.Util.Version
public import Lake.Config.Artifact
import Lake.Config.InstallPath
import Lake.Build.Actions
import Lake.Util.Url
import Lake.Util.Proc
import Lake.Util.Reservoir
import Lake.Util.JsonObject
import Lake.Util.IO
import Init.System.Platform
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
  | .bool _ => -- boolean metadata is allowed (as of 2025-03-13)
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

/-! ## Cache Service Name -/

/-- The type of service identifiers used by the Lake ache. -/
public structure CacheServiceName where
  private mk ::
    private raw : String

namespace CacheServiceName

/-- The identifier used for the default Reservoir service (i.e., `reservoir`). -/
public def reservoir : CacheServiceName := ⟨"reservoir"⟩

/-- Constructs a service identifier from a user-provided name. -/
@[inline] public def ofString (s : String) : CacheServiceName := ⟨s⟩

/-- Returns the string representation of the service identifier. -/
@[inline] public protected def toString (self : CacheServiceName) : String :=
  self.raw

public instance : ToString CacheServiceName := ⟨CacheServiceName.toString⟩

@[inline] protected def fromJson? (j : Json) : Except String CacheServiceName :=
  .mk <$> fromJson? j

instance : FromJson CacheServiceName := ⟨CacheServiceName.fromJson?⟩

@[inline] protected def toJson (self : CacheServiceName) : Json :=
  toJson self.raw

instance : ToJson CacheServiceName := ⟨CacheServiceName.toJson⟩

end CacheServiceName

/-! ## Cache Service Scope -/

inductive CacheServiceScopeImpl
| str (s : String)
| repo (s : String)

/-- The type of artifact prefixes in a Lake cache service. -/
public structure CacheServiceScope where
  private mk ::
    private impl : CacheServiceScopeImpl

namespace CacheServiceScope

/-- Constructs a generic service scope from a user-provided string. -/
public def ofString (s : String) : CacheServiceScope := ⟨.str s⟩

/-- Constructs a service scope from a GitHub repository name. -/
public def ofRepo (fullName : String) : CacheServiceScope := ⟨.repo fullName⟩

/-- Returns whether this is a repository scope. -/
public protected def isRepo (self : CacheServiceScope) : Bool :=
  match self.impl with
  | .repo .. => true
  | _ => false

/-- Returns a string representation of the scope. -/
public protected def toString (self : CacheServiceScope) : String :=
  match self.impl with
  | .str s => s
  | .repo s => s

public instance : ToString CacheServiceScope := ⟨CacheServiceScope.toString⟩

/-- Returns a JSON representation of the scope. -/
protected def toJson (self : CacheServiceScope) : Json :=
  match self.impl with
  | .str s => s
  | .repo s => s

instance : ToJson CacheServiceScope := ⟨CacheServiceScope.toJson⟩

end CacheServiceScope

/-! ## Cache Output -/

/-- The current version of the output file format. -/
public def CacheOutput.schemaVersion : String := "2026-02-25"

public structure CacheOutput where
  private mk ::
    data : Json
    service? : Option CacheServiceName := none
    scope? : Option CacheServiceScope := none
    deriving Inhabited

namespace CacheOutput

/-- **For internal use only.** -/
@[inline] public def ofData (data : Json) : CacheOutput := {data}

public protected def toJson (out : CacheOutput) : Json := Id.run do
  let mut obj :=
    JsonObject.empty
    |>.insert "schemaVersion" schemaVersion
    |>.insert "service" out.service?
  if let some scope := out.scope? then
    obj := obj.insert (if scope.isRepo then "repo" else "scope") scope.toJson
  return obj.insert "data" out.data

public instance : ToJson CacheOutput := ⟨CacheOutput.toJson⟩

public protected def fromJson? (json : Json) : Except String CacheOutput := do
  if let .obj obj := json then
    let obj := JsonObject.mk obj
    if obj.contains "schemaVersion" then
      -- presumably the new format
      -- (the edge case of a custom output with a `schemaVersion` is not worth covering)
      let data ← obj.get "data"
      let service? ← obj.get? "service"
      let repo? : Option String ← obj.get? "repo"
      let scope? ← id do
        if let some repo := repo? then
          return some (.ofRepo repo)
        else if let some scope ← obj.get? "scope" then
          return some (.ofString scope)
        else
          return none
      return {data, service?, scope?}
  -- old format: just the data
  return .ofData json

public instance : FromJson CacheOutput := ⟨CacheOutput.fromJson?⟩

end CacheOutput

/-! ## Local Cache -/

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
@[deprecated "Deprecated without replacelement." (since := "2025-03-04")]
public def getArtifact? (cache : Cache) (descr : ArtifactDescr) : BaseIO (Option Artifact) := do
  let path := cache.artifactDir / descr.relPath
  let .ok mtime ← getMTime path |>.toBaseIO
    | return none
  return some {descr, path, mtime}

/-- Returns the artifact in the Lake cache corresponding the given artifact description. Errors if missing. -/
@[deprecated "Deprecated without replacelement." (since := "2025-03-04")]
public def getArtifact (cache : Cache) (descr : ArtifactDescr) : EIO String Artifact := do
  let path := cache.artifactDir / descr.relPath
  match (← getMTime path |>.toBaseIO) with
  | .ok mtime =>
    return {descr, path, mtime}
  | .error (.noFileOrDirectory ..) =>
    error s!"artifact not found in cache: {path}"
  | .error e =>
    error s!"failed to retrieve artifact from cache: {e}"

/--
**For internal use only.**
Returns path to the artifact for each output. Errors if any are missing.
-/
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
  (cache : Cache) (scope : String) (inputHash : Hash) (out : Json)
  (service? : Option CacheServiceName) (remoteScope? : Option CacheServiceScope)
: IO Unit := do
  let file := cache.outputsFile scope inputHash
  createParentDirs file
  let out := {service?, scope? := remoteScope?, data := out : CacheOutput}
  IO.FS.writeFile file (toJson out).pretty

/-- Cache the outputs corresponding to the given input for the package.  -/
@[inline] public def writeOutputs
  [ToJson α] (cache : Cache) (scope : String) (inputHash : Hash) (outputs : α)
: IO Unit := cache.writeOutputsCore scope inputHash (toJson outputs) none none

/-- Cache the input-to-outputs mappings from a `CacheMap`.  -/
public def writeMap
  (cache : Cache) (scope : String) (map : CacheMap)
  (service? : Option CacheServiceName := none) (remoteScope? : Option CacheServiceScope := none)
: IO Unit := map.forM fun i o => cache.writeOutputsCore scope i o service? remoteScope?

/-- Retrieve the cached outputs corresponding to the given input for the package (if any). -/
public def readOutputs? (cache : Cache) (scope : String) (inputHash : Hash) : LogIO (Option CacheOutput) := do
  let path := cache.outputsFile scope inputHash
  match (← IO.FS.readFile path |>.toBaseIO) with
  | .ok contents =>
    match Json.parse contents >>= fromJson? with
    | .ok out =>
      return out
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

/-- The type of platform identifiers used by the Lake ache. -/
public structure CachePlatform where
  private mk ::
    private raw : String

namespace CachePlatform

/-- An indicator that no platform should be included in a cache scope. -/
public def none : CachePlatform := ⟨""⟩

/-- Returns `true` if this platform identifier is the `none` indicator. -/
@[inline] public def isNone (self : CachePlatform) : Bool := self.raw.isEmpty

/-- The identifier of the host platform (e.g., `System.Platform.target`). -/
public def system : CachePlatform := ⟨System.Platform.target⟩

/-- Constructs a platform identifier from a user-provided string. -/
@[inline] public def ofString (s : String) : CachePlatform := ⟨s⟩

/-- Returns the length of the platform identifier in Unicode code points. -/
public def length (self : CachePlatform) : Nat := self.raw.length

/-- Returns a string representation of the platform identifier. -/
public protected def toString (self : CachePlatform) : String :=
  if self.isNone then "none" else self.raw

instance : ToString CachePlatform := ⟨CachePlatform.toString⟩

end CachePlatform

/-- The type of toolchain identifiers used by the Lake ache. -/
public structure CacheToolchain where
  private mk ::
    private raw : String

namespace CacheToolchain

/-- An indicator that no toolchain should be included in a cache scope. -/
public def none : CacheToolchain := ⟨""⟩

/-- Returns `true` if this toolchain identifier is the `none` indicator. -/
@[inline] public def isNone (self : CacheToolchain) : Bool := self.raw.isEmpty

/-- Constructs a toolchain identifier from a user-provided string. -/
public def ofString (s : String) : CacheToolchain := ⟨normalizeToolchain s⟩

/-- **For internal use only.** See `Lake.Env.cacheToolchain`. -/
@[inline] public def ofElanToolchain (s : String) : CacheToolchain := ⟨s⟩

/-- Returns the length of the toolchain identifier in Unicode code points. -/
public def length (self : CacheToolchain) : Nat := self.raw.length

/-- Returns a string representation of the toolchain identifier. -/
public protected def toString (self : CacheToolchain) : String :=
  if self.isNone then "none" else self.raw

instance : ToString CacheToolchain := ⟨CacheToolchain.toString⟩

end CacheToolchain

/-! ## Remote Cache Service -/

/-- **For internal use only.** -/
public def downloadArtifactCore (hash : Hash) (url : String) (path : FilePath) : LogIO Unit := do
  download url path
  let actualHash ← computeFileHash path
  if actualHash != hash then
    logError s!"{path}: downloaded artifact does not have the expected hash"
    IO.FS.removeFile path
    failure

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
      | .ok none => error s!"curl's JSON output did not contain a response code; JSON received:\n{out.stderr}"
      | .error e => error s!"curl's JSON output contained an invalid JSON response code: {e}; JSON received:\n{out.stderr}"
    unless code == 200 do
      error s!"failed to upload artifact, error {code}; received:\n{out.stdout}"
  | .error e =>
    error s!"curl produced invalid JSON output: {e}; received:\n{out.stderr}"

private structure CacheServiceImpl where
  mk ::
    name? : Option CacheServiceName := none
    /- S3 Bucket -/
    key : String := ""
    artifactEndpoint : String := ""
    revisionEndpoint : String := ""
    /- Reservoir -/
    isReservoir : Bool := false
    apiEndpoint : String := ""
    deriving Nonempty

/--
Configuration of a remote cache service (e.g., Reservoir or an S3 bucket).

A given configuration is not required to support all cache service functions, and no validation
of the configuration is performed by its operations. Users should construct a service that supports
the desired functions by using `CacheService`'s smart constructors
(e.g., `reservoir`, `uploadService`).
-/
public structure CacheService where
  private mk ::
    private impl : CacheServiceImpl
    deriving Nonempty

namespace CacheService

/-- Returns the name (if any) used to identify the service. -/
@[inline] public def name? (service : CacheService) : Option CacheServiceName :=
  service.impl.name?

/-- Returns whether this is a Reservoir cache service configuration. -/
@[inline] public def isReservoir (service : CacheService) : Bool :=
  service.impl.isReservoir

/-! ### Constructors -/

/-- Constructs a `CacheService` for a Reservoir endpoint. -/
@[inline] public def reservoirService
  (apiEndpoint : String) (name? := some CacheServiceName.reservoir)
: CacheService := .mk {name?, isReservoir := true, apiEndpoint}

/-- Constructs a `CacheService` to upload artifacts and/or outputs to an S3 endpoint. -/
@[inline] public def uploadService
  (key artifactEndpoint revisionEndpoint : String)
: CacheService := .mk {key, artifactEndpoint, revisionEndpoint}

/-- Constructs a `CacheService` to download artifacts and/or outputs from an S3 endpoint. -/
@[inline] public def downloadService
  (artifactEndpoint revisionEndpoint : String) (name? : Option CacheServiceName := none)
: CacheService := .mk {name?, artifactEndpoint, revisionEndpoint}

/-- Constructs a `CacheService` to download just artifacts from an S3 endpoint. -/
@[inline] public def downloadArtsService
  (artifactEndpoint : String) (name? : Option CacheServiceName := none)
: CacheService := .mk {name?, artifactEndpoint}

/-- Reconfigures the cache service to use the provided key (for uploads).-/
@[inline] public def withKey (service : CacheService) (key : String) : CacheService :=
  .mk {service.impl with key}

/-! ### Artifact Transfer -/

/-- The MIME type of a Lake/Reservoir artifact. -/
public def artifactContentType : String := "application/vnd.reservoir.artifact"

private def appendScope (endpoint : String) (scope : String) : String :=
  scope.split '/' |>.fold (init := endpoint) fun s component =>
    uriEncode component.copy (s.push '/')

private def s3ArtifactUrl (contentHash : Hash) (service : CacheService) (scope : CacheServiceScope) : String :=
  let endpoint :=
    match scope.impl with
    | .repo scope => appendScope service.impl.artifactEndpoint scope
    | .str scope => appendScope service.impl.artifactEndpoint scope
  s!"{endpoint}/{contentHash.hex}.art"

public def artifactUrl (contentHash : Hash) (service : CacheService) (scope : CacheServiceScope) : String :=
  if service.isReservoir then
    let endpoint :=
      match scope.impl with
      | .repo scope => appendScope s!"{service.impl.apiEndpoint}/repositories" scope
      | .str scope => appendScope s!"{service.impl.apiEndpoint}/packages" scope
    s!"{endpoint}/artifacts/{contentHash.hex}.art"
  else
    service.s3ArtifactUrl contentHash scope

public def downloadArtifact
  (descr : ArtifactDescr) (cache : Cache)
  (service : CacheService) (scope : CacheServiceScope) (force := false)
: LoggerIO Unit := do
  let url := service.artifactUrl descr.hash scope
  let path := cache.artifactDir / descr.relPath
  if (← path.pathExists) && !force then
    return
  logInfo s!"\
    {scope}: downloading artifact {descr.hash}\
    \n  local path: {path}\
    \n  remote URL: {url}"
  downloadArtifactCore descr.hash url path

public def downloadArtifacts
   (descrs : Array ArtifactDescr) (cache : Cache)
   (service : CacheService) (scope : CacheServiceScope) (force := false)
: LoggerIO Unit := do
  let ok ← descrs.foldlM (init := true) fun ok descr =>
    try
      service.downloadArtifact descr cache scope force
      return ok
    catch _ =>
      return false
  unless ok do
    error s!"{scope}: failed to download some artifacts"

@[deprecated "Deprecated without replacement." (since := "2026-02-27")]
public def downloadOutputArtifacts
  (map : CacheMap) (cache : Cache) (service : CacheService)
  (localScope : String) (remoteScope : CacheServiceScope) (force := false)
: LoggerIO Unit := do
  cache.writeMap localScope map service.name? remoteScope
  let descrs ← map.collectOutputDescrs
  service.downloadArtifacts descrs cache remoteScope force

public def uploadArtifact
  (contentHash : Hash) (art : FilePath) (service : CacheService) (scope : CacheServiceScope)
: LoggerIO Unit := do
  let url := service.s3ArtifactUrl contentHash scope
  logInfo s!"\
    {scope}: uploading artifact {contentHash}\
    \n  local path: {art}\
    \n  remote URL: {url}"
  uploadS3 art artifactContentType url service.impl.key

public def uploadArtifacts
  (descrs : Vector ArtifactDescr n) (paths : Vector FilePath n)
  (service : CacheService) (scope : CacheServiceScope)
: LoggerIO Unit := n.forM fun n h => service.uploadArtifact descrs[n].hash paths[n] scope

/-! ### Output Transfer -/

/-- The MIME type of a Lake/Reservoir input-to-output mappings for a Git revision. -/
public def mapContentType : String := "application/vnd.reservoir.outputs+json-lines"

private def s3RevisionUrl
  (rev : String) (service : CacheService) (scope : CacheServiceScope)
  (platform := CachePlatform.none) (toolchain := CacheToolchain.none)
: String :=
  match scope.impl with
  | .str s => appendScope service.impl.revisionEndpoint s ++ s!"/{rev}.jsonl"
  | .repo s => Id.run do
    let mut url := appendScope service.impl.revisionEndpoint s
    unless platform.isNone do
      url := uriEncode platform.raw s!"{url}/pt/"
    unless toolchain.isNone do
      url := uriEncode (toolchain2Dir toolchain.raw).toString s!"{url}/tc/"
    return s!"{url}/{rev}.jsonl"

public def revisionUrl
  (rev : String) (service : CacheService) (scope : CacheServiceScope)
  (platform := CachePlatform.none) (toolchain := CacheToolchain.none)
: String :=
  if service.isReservoir then Id.run do
    let mut url :=
      match scope.impl with
      | .str s => appendScope s!"{service.impl.apiEndpoint}/packages" s
      | .repo s => appendScope s!"{service.impl.apiEndpoint}/repositories" s
    url := s!"{url}/build-outputs?rev={rev}"
    unless platform.isNone do
      url := uriEncode platform.raw s!"{url}&platform="
    unless toolchain.isNone do
      url := uriEncode toolchain.raw s!"{url}&toolchain="
    return url
  else
    service.s3RevisionUrl rev scope platform toolchain

public def downloadRevisionOutputs?
  (rev : String) (cache : Cache) (service : CacheService)
  (localScope : String) (remoteScope : CacheServiceScope)
  (platform := CachePlatform.none) (toolchain := CacheToolchain.none) (force := false)
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
  (rev : String) (outputs : FilePath) (service : CacheService) (scope : CacheServiceScope)
  (platform := CachePlatform.none) (toolchain := CacheToolchain.none)
: LoggerIO Unit := do
  let url := service.s3RevisionUrl rev scope platform toolchain
  logInfo s!"\
    {scope}: uploading build outputs for revision {rev}\
    \n  local path: {outputs}\
    \n  remote URL: {url}"
  uploadS3 outputs mapContentType url service.impl.key

end CacheService
