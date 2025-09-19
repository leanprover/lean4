/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.System.IO
public import Lake.Util.Exit
public import Lake.Load.Config
public import Lake.CLI.Error
import Lake.Version
import Lake.Build.Run
import Lake.Build.Targets
import Lake.Build.Job.Monad
import Lake.Build.Job.Register
import Lake.Build.Target.Fetch
import Lake.Load.Package
import Lake.Load.Workspace
import Lake.Util.IO
import Lake.Util.Git
import Lake.Util.Error
import Lake.Util.MainM
import Lake.Util.Cli
import Lake.CLI.Init
import Lake.CLI.Help
import Lake.CLI.Build
import Lake.CLI.Error
import Lake.CLI.Actions
import Lake.CLI.Translate
import Lake.CLI.Serve

-- # CLI

open System
open Lean (Json toJson fromJson? NameMap)

namespace Lake

/-! ## General options for top-level `lake` -/

public structure LakeOptions where
  args : List String := []
  rootDir : FilePath := "."
  configFile : FilePath := defaultConfigFile
  elanInstall? : Option ElanInstall := none
  leanInstall? : Option LeanInstall := none
  lakeInstall? : Option LakeInstall := none
  configOpts : NameMap String := {}
  packageOverrides : Array PackageEntry := #[]
  subArgs : List String := []
  wantsHelp : Bool := false
  verbosity : Verbosity := .normal
  updateDeps : Bool := false
  updateToolchain : Bool := true
  reconfigure : Bool := false
  oldMode : Bool := false
  trustHash : Bool := true
  noBuild : Bool := false
  noCache : Option Bool := none
  failLv : LogLevel := .error
  outLv? : Option LogLevel := .none
  ansiMode : AnsiMode := .auto
  outFormat : OutFormat := .text
  offline : Bool := false
  outputsFile? : Option FilePath := none
  forceDownload : Bool := false
  scope? : Option String := none
  rev? : Option String := none
  maxRevs : Nat := 100

def LakeOptions.outLv (opts : LakeOptions) : LogLevel :=
  opts.outLv?.getD opts.verbosity.minLogLv

/-- Get the Lean installation. Error if missing. -/
def LakeOptions.getLeanInstall (opts : LakeOptions) : Except CliError LeanInstall :=
  match opts.leanInstall? with
  | none => .error CliError.unknownLeanInstall
  | some lean => .ok lean

/-- Get the Lake installation. Error if missing. -/
def LakeOptions.getLakeInstall (opts : LakeOptions) : Except CliError LakeInstall :=
  match opts.lakeInstall? with
  | none => .error CliError.unknownLakeInstall
  | some lake => .ok lake

/-- Get the Lean and Lake installation. Error if either is missing. -/
def LakeOptions.getInstall (opts : LakeOptions) : Except CliError (LeanInstall × LakeInstall) := do
  return (← opts.getLeanInstall, ← opts.getLakeInstall)

/-- Compute the Lake environment based on `opts`. Error if an install is missing. -/
def LakeOptions.computeEnv (opts : LakeOptions) : EIO CliError Lake.Env := do
  Env.compute (← opts.getLakeInstall) (← opts.getLeanInstall) opts.elanInstall?
    opts.noCache |>.adaptExcept fun msg => .invalidEnv msg

/-- Make a `LoadConfig` from a `LakeOptions`. -/
public def LakeOptions.mkLoadConfig (opts : LakeOptions) : EIO CliError LoadConfig := do
  let some wsDir ← resolvePath? opts.rootDir
    | throw <| .missingRootDir opts.rootDir
  return {
    lakeArgs? := opts.args.toArray
    lakeEnv := ← opts.computeEnv
    wsDir
    relConfigFile := opts.configFile
    packageOverrides := opts.packageOverrides
    lakeOpts := opts.configOpts
    leanOpts := Lean.Options.empty
    reconfigure := opts.reconfigure
    updateDeps := opts.updateDeps
    updateToolchain := opts.updateToolchain
  }

/-- Make a `BuildConfig` from a `LakeOptions`. -/
def LakeOptions.mkBuildConfig
  (opts : LakeOptions) (out := OutStream.stderr) (showSuccess := false)
: BuildConfig where
  oldMode := opts.oldMode
  trustHash := opts.trustHash
  noBuild := opts.noBuild
  verbosity := opts.verbosity
  failLv := opts.failLv
  outLv := opts.outLv
  ansiMode := opts.ansiMode
  outputsFile? := opts.outputsFile?
  out; showSuccess

export LakeOptions (mkLoadConfig mkBuildConfig)

/-! ## Monad -/

abbrev CliMainM := ExceptT CliError MainM
abbrev CliStateM := StateT LakeOptions CliMainM
abbrev CliM := ArgsT CliStateM

def CliM.run (self : CliM α) (args : List String) : BaseIO ExitCode := do
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let main := self.run' args |>.run' {args, elanInstall?, leanInstall?, lakeInstall?}
  let main := main.run >>= fun | .ok a => pure a | .error e => error e.toString
  main.run

@[inline] def CliStateM.runLogIO (x : LogIO α) : CliStateM α := do
  let opts ← get
  MainM.runLogIO x opts.outLv opts.ansiMode

instance (priority := low) : MonadLift LogIO CliStateM := ⟨CliStateM.runLogIO⟩

@[inline] def CliStateM.runLoggerIO (x : LoggerIO α) : CliStateM α := do
  let opts ← get
  MainM.runLoggerIO x opts.outLv opts.ansiMode

instance (priority := low) : MonadLift LoggerIO CliStateM := ⟨CliStateM.runLoggerIO⟩

/-! ## Argument Parsing -/

def takeArg (arg : String) : CliM String := do
  match (← takeArg?) with
  | none => throw <| CliError.missingArg arg
  | some arg => pure arg

def takeOptArg (opt arg : String) : CliM String := do
  match (← takeArg?) with
  | none => throw <| CliError.missingOptArg opt arg
  | some arg => pure arg

@[inline] def takeOptArg' (opt arg : String) (f : String → Option α)  : CliM α := do
  if let some a :=  f (← takeOptArg opt arg) then return a
  throw <| CliError.invalidOptArg opt arg

/--
Verify that there are no CLI arguments remaining
before running the given action.
-/
def noArgsRem (act : CliStateM α) : CliM α := do
  let args ← getArgs
  if args.isEmpty then act else
    throw <| CliError.unexpectedArguments args

/-! ## Option Parsing -/

def getWantsHelp : CliStateM Bool :=
  (·.wantsHelp) <$> get

def setConfigOpt (kvPair : String) : CliM PUnit :=
  let pos := kvPair.posOf '='
  let (key, val) :=
    if pos = kvPair.endPos then
      (kvPair.toName, "")
    else
      (kvPair.extract 0 pos |>.toName, kvPair.extract (kvPair.next pos) kvPair.endPos)
  modifyThe LakeOptions fun opts =>
    {opts with configOpts := opts.configOpts.insert key val}

def lakeShortOption : (opt : Char) → CliM PUnit
| 'q' => modifyThe LakeOptions ({· with verbosity := .quiet})
| 'v' => modifyThe LakeOptions ({· with verbosity := .verbose})
| 'd' => do let rootDir ← takeOptArg "-d" "path"; modifyThe LakeOptions ({· with rootDir})
| 'f' => do let configFile ← takeOptArg "-f" "path"; modifyThe LakeOptions ({· with configFile})
| 'o' => do let outputsFile? ← takeOptArg "-o" "path"; modifyThe LakeOptions ({· with outputsFile?})
| 'K' => do setConfigOpt <| ← takeOptArg "-K" "key-value pair"
| 'U' => do
  logWarning "the '-U' shorthand for '--update' is deprecated"
  modifyThe LakeOptions ({· with updateDeps := true})
| 'R' => modifyThe LakeOptions ({· with reconfigure := true})
| 'h' => modifyThe LakeOptions ({· with wantsHelp := true})
| 'H' => modifyThe LakeOptions ({· with trustHash := false})
| 'J' => modifyThe LakeOptions ({· with outFormat := .json})
| opt => throw <| CliError.unknownShortOption opt

def lakeLongOption : (opt : String) → CliM PUnit
| "--quiet"       => modifyThe LakeOptions ({· with verbosity := .quiet})
| "--verbose"     => modifyThe LakeOptions ({· with verbosity := .verbose})
| "--update"      => modifyThe LakeOptions ({· with updateDeps := true})
| "--keep-toolchain" => modifyThe LakeOptions ({· with updateToolchain := false})
| "--reconfigure" => modifyThe LakeOptions ({· with reconfigure := true})
| "--old"         => modifyThe LakeOptions ({· with oldMode := true})
| "--text"        => modifyThe LakeOptions ({· with outFormat := .text})
| "--json"        => modifyThe LakeOptions ({· with outFormat := .json})
| "--no-build"    => modifyThe LakeOptions ({· with noBuild := true})
| "--no-cache"    => modifyThe LakeOptions ({· with noCache := true})
| "--try-cache"   => modifyThe LakeOptions ({· with noCache := false})
| "--rehash"      => modifyThe LakeOptions ({· with trustHash := false})
| "--offline"     => modifyThe LakeOptions ({· with offline := true})
| "--wfail"       => modifyThe LakeOptions ({· with failLv := .warning})
| "--iofail"      => modifyThe LakeOptions ({· with failLv := .info})
| "--force-download" => modifyThe LakeOptions ({· with forceDownload := true})
| "--scope" => do
  let scope ← takeOptArg "--scope" "cache scope"
  modifyThe LakeOptions ({· with scope? := some scope})
| "--repo" => do
  let repo ← takeOptArg "--repo" "repository"
  modifyThe LakeOptions ({· with scope? := some repo})
| "--rev" => do
  let rev ← takeOptArg "--rev" "Git revision"
  modifyThe LakeOptions ({· with rev? := some rev})
| "--max-revs" => do
  let some n ← (·.toNat?) <$> takeOptArg "--max-revs" "number of revisions"
    | error "argument to `--max-revs` should be a natural number"
  modifyThe LakeOptions ({· with maxRevs := n})
| "--log-level"   => do
  let outLv ← takeOptArg' "--log-level" "log level" LogLevel.ofString?
  modifyThe LakeOptions ({· with outLv? := outLv})
| "--fail-level"  => do
  let failLv ← takeOptArg' "--fail-level" "log level" LogLevel.ofString?
  modifyThe LakeOptions ({· with failLv})
| "--ansi"        => modifyThe LakeOptions ({· with ansiMode := .ansi})
| "--no-ansi"     => modifyThe LakeOptions ({· with ansiMode := .noAnsi})
| "--packages"    => do
  let file ← takeOptArg "--packages" "package overrides file"
  let overrides ← Manifest.loadEntries file
  modifyThe LakeOptions fun opts =>
    {opts with packageOverrides := opts.packageOverrides ++ overrides}
| "--dir"         => do
  let rootDir ← takeOptArg "--dir" "path"
  modifyThe LakeOptions ({· with rootDir})
| "--file"        => do
  let configFile ← takeOptArg "--file" "path"
  modifyThe LakeOptions ({· with configFile})
| "--help"        => modifyThe LakeOptions ({· with wantsHelp := true})
| "--"            => do
  let subArgs ← takeArgs
  modifyThe LakeOptions ({· with subArgs})
| opt             =>  throw <| CliError.unknownLongOption opt

def lakeOption :=
  option {
    short := lakeShortOption
    long := lakeLongOption
    longShort := shortOptionWithArg lakeShortOption
  }

/-! ## Actions -/

/-- Verify the Lean version Lake was built with matches that of the give Lean installation. -/
def verifyLeanVersion (leanInstall : LeanInstall) : Except CliError PUnit := do
  unless leanInstall.githash == Lean.githash do
    throw <| CliError.leanRevMismatch Lean.githash leanInstall.githash

/-- Output the detected installs and verify the Lean version. -/
def verifyInstall (opts : LakeOptions) : ExceptT CliError MainM PUnit := do
  IO.println s!"Elan:\n{repr <| opts.elanInstall?}"
  IO.println s!"Lean:\n{repr <| opts.leanInstall?}"
  IO.println s!"Lake:\n{repr <| opts.lakeInstall?}"
  let (leanInstall, _) ← opts.getInstall
  verifyLeanVersion leanInstall

def parseScriptSpec (ws : Workspace) (spec : String) : Except CliError Script :=
  match spec.splitOn "/" with
  | [scriptName] =>
    match ws.findScript? (stringToLegalOrSimpleName scriptName) with
    | some script => return script
    | none => throw <| CliError.unknownScript spec
  | [pkg, scriptName] => do
    let pkg ← parsePackageSpec ws pkg
    match pkg.scripts.find? (stringToLegalOrSimpleName scriptName) with
    | some script => return script
    | none => throw <| CliError.unknownScript spec
  | _ => throw <| CliError.invalidScriptSpec spec

def parseTemplateSpec (spec : String) : Except CliError InitTemplate := do
  if spec.isEmpty then
    return default
  else if let some tmp := InitTemplate.ofString? spec.toLower then
    return tmp
  else
    throw <| CliError.unknownTemplate spec

def parseLangSpec (spec : String) : Except CliError ConfigLang :=
  if spec.isEmpty then
    return default
  else if let some lang := ConfigLang.ofString? spec.toLower then
    return lang
  else
    throw <| CliError.unknownConfigLang spec

def parseTemplateLangSpec (spec : String) : Except CliError (InitTemplate × ConfigLang) := do
  match spec.splitOn "." with
  | [tmp, lang] => return (← parseTemplateSpec tmp, ← parseLangSpec lang)
  | [tmp] => return (← parseTemplateSpec tmp, default)
  | _ => return default


/-! ## Commands -/

namespace lake

/-! ### `lake cache` CLI -/

namespace cache

protected def get : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let mappings? ← takeArg?
  noArgsRem  do
  let cfg ← mkLoadConfig opts
  let ws ← loadWorkspace cfg
  let cache := ws.lakeCache
  if let some file := mappings? then
    let some remoteScope := opts.scope?
      | error "to use `cache get` with a mappings file, `--scope` must be set"
    let service : CacheService :=
      if let some artifactEndpoint := ws.lakeEnv.cacheArtifactEndpoint? then
        {artifactEndpoint}
      else
        {apiEndpoint? := some ws.lakeEnv.reservoirApiUrl}
    let map ← CacheMap.load file
    service.downloadOutputArtifacts map cache remoteScope ws.root.cacheScope opts.forceDownload
  else
    let service : CacheService ← id do
      match ws.lakeEnv.cacheArtifactEndpoint?, ws.lakeEnv.cacheRevisionEndpoint? with
      | some artifactEndpoint, some revisionEndpoint =>
        return {artifactEndpoint, revisionEndpoint}
      | none, none =>
        return {apiEndpoint? := some ws.lakeEnv.reservoirApiUrl}
      | some artifactEndpoint, none =>
        error (invalidEndpointConfig artifactEndpoint "")
      | none, some revisionEndpoint =>
        error (invalidEndpointConfig "" revisionEndpoint)
    if let some remoteScope := opts.scope? then
      let service := if service.apiEndpoint?.isNone then service else {
        artifactEndpoint := s!"{ws.lakeEnv.reservoirApiUrl}/artifacts"
        revisionEndpoint := s!"{ws.lakeEnv.reservoirApiUrl}/outputs"
      }
      let map ← getOutputs cache service ws.root remoteScope opts
      service.downloadOutputArtifacts map cache remoteScope ws.root.cacheScope opts.forceDownload
    else if service.apiEndpoint?.isSome then -- Reservoir
      -- TODO: Parallelize?
      let ok ← ws.packages.foldlM (start := 1) (init := true) (m := LoggerIO) fun ok pkg => do
        try
          if pkg.scope.isEmpty then
            logInfo s!"{pkg.name}: skipping non-Reservoir dependency`"
          else
            let remoteScope := s!"{pkg.scope}/{pkg.name.toString (escape := false)}"
            let map ← getOutputs cache service pkg remoteScope opts
            service.downloadOutputArtifacts map cache remoteScope pkg.cacheScope opts.forceDownload
          return ok
        catch _ =>
          return false
      unless ok do
        error "failed to download artifacts for some dependencies"
    else
      error "to use `cache get` with a custom endpoint, the `--scope` option must be set"
where
  invalidEndpointConfig artifactEndpoint revisionEndpoint :=
    s!"invalid endpoint configuration:\
    \n  LAKE_CACHE_ARTIFACT_ENDPOINT={artifactEndpoint}\
    \n  LAKE_CACHE_REVISION_ENDPOINT={revisionEndpoint}\n\
    To use `cache get` with a custom endpoint, both environment variables \
    must be set to non-empty strings. To use Reservoir, neither should be set."
  getOutputs cache service pkg remoteScope opts : LoggerIO CacheMap := do
    let repo := GitRepo.mk pkg.dir
    if let some rev := opts.rev? then
      let rev ← repo.resolveRevision rev
      let some map ← service.downloadRevisionOutputs? rev cache remoteScope
        | error s!"{remoteScope}: outputs not found for revision {rev}"
      return map
    else
      if (← repo.hasDiff) then
        logWarning s!"{pkg.name}: package has changes; \
          only artifacts for committed code will be downloaded"
        if .warning ≤ opts.failLv then
          failure
      let n := opts.maxRevs
      let revs ← repo.getHeadRevisions n
      let map? ← revs.findSomeM? fun rev =>
        service.downloadRevisionOutputs? rev cache remoteScope
      let some map := map?
        | let revisions := if n = 0 then "for any revision" else s!"in {n} revisions from HEAD"
          error s!"{remoteScope}: no outputs found {revisions}"
      return map

protected def put : CliM PUnit := do
  processOptions lakeOption
  let file ← takeArg "mappings"
  let opts ← getThe LakeOptions
  let some scope := opts.scope?
    | error "the `--scope` option must be set for `cache put`"
  noArgsRem do
  let cfg ← mkLoadConfig opts
  let ws ← loadWorkspace cfg
  let service : CacheService ← id do
    match ws.lakeEnv.cacheKey?, ws.lakeEnv.cacheArtifactEndpoint?, ws.lakeEnv.cacheRevisionEndpoint? with
    | some key, some artifactEndpoint, some revisionEndpoint =>
      return {key, artifactEndpoint, revisionEndpoint}
    | key?, artifactEndpoint?, revisionEndpoint? =>
      error (invalidEndpointConfig key? artifactEndpoint? revisionEndpoint?)
  let pkg := ws.root
  let repo := GitRepo.mk pkg.dir
  if (← repo.hasDiff) then
    logWarning s!"{pkg.name}: package has changes; \
      artifacts will be uploaded for the most recent commit"
    if .warning ≤ opts.failLv then
      exit 1
  let rev ← repo.getHeadRevision
  let map ← CacheMap.load file
  let descrs ← map.collectOutputDescrs
  let paths ← ws.lakeCache.getArtifactPaths descrs
  service.uploadArtifacts ⟨descrs, rfl⟩ paths scope
  -- Mappings are uploaded after artifacts to allow downloads to assume that
  -- if the mappings exist, the artifacts should also exist
  service.uploadRevisionOutputs rev file scope
where
  invalidEndpointConfig key? artifactEndpoint? revisionEndpoint? :=
    s!"invalid endpoint configuration:\
    \n  LAKE_CACHE_KEY is {if key?.isNone then "unset" else "set"}\
    \n  LAKE_CACHE_ARTIFACT_ENDPOINT={artifactEndpoint?.getD ""}\
    \n  LAKE_CACHE_REVISION_ENDPOINT={revisionEndpoint?.getD ""}\n\
    To use `cache put`, these environment variables must be set to non-empty strings."

protected def add : CliM PUnit := do
  processOptions lakeOption
  let file ← takeArg "mappings"
  let pkg? ← takeArg?
  let opts ← getThe LakeOptions
  noArgsRem do
  let cfg ← mkLoadConfig opts
  let ws ← loadWorkspace cfg
  let pkg ← match pkg? with
    | some pkg => parsePackageSpec ws pkg
    | _ => pure ws.root
  let scope := pkg.cacheScope
  let map ← CacheMap.load file
  ws.lakeCache.writeMap scope map

protected def help : CliM PUnit := do
  IO.println <| helpCache <| ← takeArgD ""

end cache

def cacheCli : (cmd : String) → CliM PUnit
| "add"   => cache.add
| "get"   => cache.get
| "put"   => cache.put
| "help"  => cache.help
| cmd     => throw <| CliError.unknownCommand cmd

/-! ### `lake script` CLI -/

namespace script

protected def list : CliM PUnit := do
  processOptions lakeOption
  let config ← mkLoadConfig (← getThe LakeOptions)
  noArgsRem do
    let ws ← loadWorkspace config
    ws.packages.forM fun pkg => do
      pkg.scripts.forM fun _ script =>
        IO.println script.name

protected nonrec def run : CliM PUnit := do
  processLeadingOptions lakeOption  -- between `lake [script] run` and `<name>`
  let config ← mkLoadConfig (← getThe LakeOptions)
  let ws ← loadWorkspace config
  if let some spec ← takeArg? then
    let args ← takeArgs
    let script ← parseScriptSpec ws spec
    exit <| ← script.run args |>.run {opaqueWs := ws}
  else
    for script in ws.root.defaultScripts do
      exitIfErrorCode <| ← script.run [] |>.run {opaqueWs := ws}
    exit 0

protected def doc : CliM PUnit := do
  processOptions lakeOption
  let spec ← takeArg "script name"
  let config ← mkLoadConfig (← getThe LakeOptions)
  noArgsRem do
    let ws ← loadWorkspace config
    let script ← parseScriptSpec ws spec
    match script.doc? with
    | some doc => IO.println doc
    | none => throw <| CliError.missingScriptDoc script.name

protected def help : CliM PUnit := do
  IO.println <| helpScript <| ← takeArgD ""

end script

def scriptCli : (cmd : String) → CliM PUnit
| "list"  => script.list
| "run"   => script.run
| "doc"   => script.doc
| "help"  => script.help
| cmd     => throw <| CliError.unknownCommand cmd

/-! ### `lake` CLI -/

protected def new : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let name ← takeArg "package name"
  let (tmp, lang) ← parseTemplateLangSpec <| ← takeArgD ""
  noArgsRem do new name tmp lang (← opts.computeEnv) opts.rootDir opts.offline

protected def init : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let name := ← takeArgD "."
  let (tmp, lang) ← parseTemplateLangSpec <| ← takeArgD ""
  noArgsRem do init name tmp lang (← opts.computeEnv) opts.rootDir opts.offline

protected def build : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let config ← mkLoadConfig opts
  let ws ← loadWorkspace config
  let targetSpecs ← takeArgs
  let specs ← parseTargetSpecs ws targetSpecs
  specs.forM fun spec =>
    unless spec.buildable do
      throw <| .invalidBuildTarget spec.info.key.toSimpleString
  let buildConfig := mkBuildConfig opts (out := .stdout) (showSuccess := true)
  ws.runBuild (buildSpecs specs) buildConfig

protected def checkBuild : CliM PUnit := do
  processOptions lakeOption
  let pkg ← loadPackage (← mkLoadConfig (← getThe LakeOptions))
  noArgsRem do exit <| if pkg.defaultTargets.isEmpty then 1 else 0

protected def query : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let config ← mkLoadConfig opts
  let ws ← loadWorkspace config
  let targetSpecs ← takeArgs
  let specs ← parseTargetSpecs ws targetSpecs
  let fmt := opts.outFormat
  let buildConfig := mkBuildConfig opts
  let results ← ws.runBuild (querySpecs specs fmt) buildConfig
  results.forM (IO.println ·)

protected def queryKind : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let config ← mkLoadConfig opts
  let ws ← loadWorkspace config
  let targetSpecs ← takeArgs
  let keys ← targetSpecs.toArray.mapM fun spec =>
    IO.ofExcept <| PartialBuildKey.parse spec
  let buildConfig := mkBuildConfig opts
  let r ← ws.runFetchM (cfg := buildConfig) <| keys.mapM fun key => do
    let ⟨_, job⟩ ← key.fetchInCore ws.root
    let kind := job.kind
    let job ← maybeRegisterJob key.toString job.toOpaque
    return (kind.name, job)
  r.forM (IO.println ·.1)
  r.forM fun (_, job) => do
    match (← job.wait?) with
    | some _ => pure ()
    | none => error "build failed"

protected def resolveDeps : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let config ← mkLoadConfig opts
  noArgsRem do
  discard <| loadWorkspace config

protected def update : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let config ← mkLoadConfig opts
  let toUpdate := (← getArgs).foldl (·.insert <| stringToLegalOrSimpleName ·) {}
  updateManifest config toUpdate

protected def pack : CliM PUnit := do
  processOptions lakeOption
  let file? ← takeArg?
  noArgsRem do
  let ws ← loadWorkspace (← mkLoadConfig (← getThe LakeOptions))
  let file := (FilePath.mk <$> file?).getD ws.root.buildArchiveFile
  ws.root.pack file

protected def unpack : CliM PUnit := do
  processOptions lakeOption
  let file? ← takeArg?
  noArgsRem do
  let ws ← loadWorkspace (← mkLoadConfig (← getThe LakeOptions))
  let file := (FilePath.mk <$> file?).getD ws.root.buildArchiveFile
  ws.root.unpack file

protected def upload : CliM PUnit := do
  processOptions lakeOption
  let tag ← takeArg "release tag"
  noArgsRem do
  let ws ← loadWorkspace (← mkLoadConfig (← getThe LakeOptions))
  ws.root.uploadRelease tag

protected def cache : CliM PUnit := do
  if let some cmd ← takeArg? then
    processLeadingOptions lakeOption -- between `lake cache <cmd>` and args
    if (← getWantsHelp) then
      IO.println <| helpCache cmd
    else
      cacheCli cmd
  else
    throw <| CliError.missingCommand

protected def setupFile : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let loadConfig ← mkLoadConfig opts
  let buildConfig := mkBuildConfig opts
  let filePath ← takeArg "file path"
  let header? ← takeArg?
  noArgsRem do
  let header ← header?.mapM  fun header => do
    let header ← if header == "-" then IO.getStdin >>= (·.getLine) else pure header
    match Json.parse header >>= fromJson? with
    | .ok header => pure header
    | .error e => error s!"failed to parse header JSON: {e}"
  setupFile loadConfig filePath header buildConfig

protected def test : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let ws ← loadWorkspace (← mkLoadConfig opts)
  noArgsRem do
  let x := ws.root.test opts.subArgs (mkBuildConfig opts)
  exit <| ← x.run (mkLakeContext ws)

protected def checkTest : CliM PUnit := do
  processOptions lakeOption
  let pkg ← loadPackage (← mkLoadConfig (← getThe LakeOptions))
  noArgsRem do exit <| if pkg.testDriver.isEmpty then 1 else 0

protected def lint : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let ws ← loadWorkspace (← mkLoadConfig opts)
  noArgsRem do
  let x := ws.root.lint opts.subArgs (mkBuildConfig opts)
  exit <| ← x.run (mkLakeContext ws)

protected def checkLint : CliM PUnit := do
  processOptions lakeOption
  let pkg ← loadPackage (← mkLoadConfig (← getThe LakeOptions))
  noArgsRem do exit <| if pkg.lintDriver.isEmpty then 1 else 0

protected def clean : CliM PUnit := do
  processOptions lakeOption
  let config ← mkLoadConfig (← getThe LakeOptions)
  let ws ← loadWorkspace config
  let pkgSpecs ← takeArgs
  if pkgSpecs.isEmpty then
    ws.clean
  else
    let pkgs ← pkgSpecs.mapM fun pkgSpec =>
      match ws.findPackage? <| stringToLegalOrSimpleName pkgSpec with
      | none => throw <| .unknownPackage pkgSpec
      | some pkg => pure pkg.toPackage
    pkgs.forM (·.clean)

protected def script : CliM PUnit := do
  if let some cmd ← takeArg? then
    processLeadingOptions lakeOption -- between `lake script <cmd>` and args
    if (← getWantsHelp) then
      IO.println <| helpScript cmd
    else
      scriptCli cmd
  else
    throw <| CliError.missingCommand

protected def serve : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let args := opts.subArgs.toArray
  let config ← mkLoadConfig opts
  noArgsRem do exit <| ← serve config args

protected def env : CliM PUnit := do
  let config ← mkLoadConfig (← getThe LakeOptions)
  let env ← do
    if (← configFileExists config.configFile) then
      pure (← loadWorkspace config).augmentedEnvVars
    else
      pure config.lakeEnv.vars
  if let some cmd ← takeArg? then
    let child ← IO.Process.spawn {cmd, args := (← takeArgs).toArray, env}
    exit <| ← child.wait
  else
    env.forM fun (var, val?) =>
      IO.println s!"{var}={val?.getD ""}"
    exit 0

protected def exe : CliM PUnit := do
  let exeSpec ← takeArg "executable target"
  let args ← takeArgs
  let opts ← getThe LakeOptions
  let config ← mkLoadConfig opts
  let ws ← loadWorkspace config
  let exe ← parseExeTargetSpec ws exeSpec
  let exeFile ← ws.runBuild exe.fetch (mkBuildConfig opts)
  exit <| ← (Lake.env exeFile.toString args.toArray).run <| mkLakeContext ws

protected def lean : CliM PUnit := do
  processOptions lakeOption
  let leanFile ← takeArg "Lean file"
  let opts ← getThe LakeOptions
  noArgsRem do
  let ws ← loadWorkspace (← mkLoadConfig opts)
  let rc ← ws.evalLeanFile leanFile opts.subArgs.toArray (mkBuildConfig opts)
  exit rc

protected def translateConfig : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let cfg ← mkLoadConfig opts
  let lang ← parseLangSpec (← takeArg "configuration language")
  let outFile? := (← takeArg?).map FilePath.mk
  noArgsRem do
  let pkg ← loadPackage cfg
  let outFile := outFile?.getD <| pkg.configFile.withExtension lang.fileExtension
  if (← outFile.pathExists) then
    throw (.outputConfigExists outFile)
  IO.FS.writeFile outFile (← pkg.mkConfigString lang)
  if outFile?.isNone then
    IO.FS.rename pkg.configFile (pkg.configFile.addExtension "bak")

def ReservoirConfig.currentSchemaVersion : StdVer := {major := 1}

structure ReservoirConfig where
  name : String
  version : StdVer
  versionTags : List String
  description : String
  keywords : Array String
  homepage : String
  platformIndependent : Option Bool
  license : String
  licenseFiles : Array FilePath
  readmeFile : Option FilePath
  doIndex : Bool
  schemaVersion := ReservoirConfig.currentSchemaVersion
  deriving Lean.ToJson

protected def reservoirConfig : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let cfg ← mkLoadConfig opts
  let _ ← id do
    let some verStr ← takeArg?
      | return ReservoirConfig.currentSchemaVersion
    match StdVer.parse verStr with
    | .ok ver => return ver
    | .error e => error s!"invalid target version: {e}"
  noArgsRem do
  let pkg ← loadPackage cfg
  let repoTags ← GitRepo.getTags pkg.dir
  let licenseFiles ← pkg.licenseFiles.filterMapM fun relPath => do
    return if (← (pkg.dir / relPath).pathExists) then some relPath else none
  let readmeFile :=
    if (← pkg.readmeFile.pathExists) then some pkg.relReadmeFile else none
  let cfg : ReservoirConfig := {
    name := pkg.name.toString
    version := pkg.version
    versionTags := repoTags.filter pkg.versionTags.matches
    description := pkg.description
    homepage := pkg.homepage
    keywords := pkg.keywords
    platformIndependent := pkg.platformIndependent
    license := pkg.license
    licenseFiles := licenseFiles
    readmeFile := readmeFile
    doIndex := pkg.reservoir
  }
  IO.println (toJson cfg).pretty

protected def versionTags : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let cfg ← mkLoadConfig opts
  noArgsRem do
  let pkg ← loadPackage cfg
  let tags ← GitRepo.getTags pkg.dir
  for tag in tags do
    if pkg.versionTags.matches tag then
      IO.println tag

protected def selfCheck : CliM PUnit := do
  processOptions lakeOption
  noArgsRem do verifyInstall (← getThe LakeOptions)

protected def help : CliM PUnit := do
  IO.println <| help <| ← takeArgD ""

end lake

def lakeCli : (cmd : String) → CliM PUnit
| "new"                 => lake.new
| "init"                => lake.init
| "build"               => lake.build
| "check-build"         => lake.checkBuild
| "query"               => lake.query
| "query-kind"          => lake.queryKind
| "update" | "upgrade"  => lake.update
| "resolve-deps"        => lake.resolveDeps
| "pack"                => lake.pack
| "unpack"              => lake.unpack
| "upload"              => lake.upload
| "cache"               => lake.cache
| "setup-file"          => lake.setupFile
| "test"                => lake.test
| "check-test"          => lake.checkTest
| "lint"                => lake.lint
| "check-lint"          => lake.checkLint
| "clean"               => lake.clean
| "script"              => lake.script
| "scripts"             => lake.script.list
| "run"                 => lake.script.run
| "serve"               => lake.serve
| "env"                 => lake.env
| "exe" | "exec"        => lake.exe
| "lean"                => lake.lean
| "translate-config"    => lake.translateConfig
| "reservoir-config"    => lake.reservoirConfig
| "version-tags"        => lake.versionTags
| "self-check"          => lake.selfCheck
| "help"                => lake.help
| cmd                   =>
  if cmd.startsWith "+" then
    throw <| CliError.unexpectedPlus
  else
    throw <| CliError.unknownCommand cmd

def lake : CliM PUnit := do
  match (← getArgs) with
  | [] => IO.println usage
  | ["--version"] => IO.println uiVersionString
  | _ => -- normal CLI
    processLeadingOptions lakeOption -- between `lake` and command
    if let some cmd ← takeArg? then
      processLeadingOptions lakeOption -- between `lake <cmd>` and args
      if (← getWantsHelp) then
        IO.println <| help cmd
      else
        lakeCli cmd
    else
      if (← getWantsHelp) then
        IO.println usage
      else
        throw <| CliError.missingCommand

public def cli (args : List String) : BaseIO ExitCode :=
  inline <| (lake).run args
