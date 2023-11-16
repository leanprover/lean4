/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Elab.Frontend
import Lake.DSL.Extensions
import Lake.Load.Config
import Lake.Build.Trace
import Lake.Util.Platform
import Lake.Util.Log

namespace Lake
open Lean System

deriving instance BEq, Hashable for Import

/- Cache for the imported header environment of Lake configuration files. -/
initialize importEnvCache : IO.Ref (HashMap (Array Import) Environment) ← IO.mkRef {}

/-- Like `importModules`, but fetch the resulting import state from the cache if possible. -/
def importModulesUsingCache (imports : Array Import) (opts : Options) (trustLevel : UInt32) : IO Environment := do
  if let some env := (← importEnvCache.get).find? imports then
    return env
  let env ← importModules imports opts trustLevel
  importEnvCache.modify (·.insert imports env)
  return env

/-- Like `Lean.Elab.processHeader`, but using `importEnvCache`. -/
def processHeader (header : Syntax) (opts : Options)
(inputCtx : Parser.InputContext) : StateT MessageLog IO Environment := do
  try
    let imports := Elab.headerToImports header
    importModulesUsingCache imports opts 1024
  catch e =>
    let pos := inputCtx.fileMap.toPosition <| header.getPos?.getD 0
    modify (·.add { fileName := inputCtx.fileName, data := toString e, pos })
    mkEmptyEnvironment

/-- Main module `Name` of a Lake configuration file. -/
def configModuleName : Name := `lakefile

/-- Elaborate `configFile` with the given package directory and options. -/
def elabConfigFile (pkgDir : FilePath) (lakeOpts : NameMap String)
(leanOpts := Options.empty) (configFile := pkgDir / defaultConfigFile) : LogIO Environment := do

  -- Read file and initialize environment
  let input ← IO.FS.readFile configFile
  let inputCtx := Parser.mkInputContext input configFile.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header leanOpts inputCtx messages
  let env := env.setMainModule configModuleName

  -- Configure extensions
  let env := dirExt.setState env pkgDir
  let env := optsExt.setState env lakeOpts

  -- Elaborate File
  let commandState := Elab.Command.mkState env messages leanOpts
  let s ← Elab.IO.processCommands inputCtx parserState commandState

  -- Log messages
  for msg in s.commandState.messages.toList do
    match msg.severity with
    | MessageSeverity.information => logInfo (← msg.toString)
    | MessageSeverity.warning     => logWarning (← msg.toString)
    | MessageSeverity.error       => logError (← msg.toString)

  -- Check result
  if s.commandState.messages.hasErrors then
    error s!"{configFile}: package configuration has errors"
  else
    return s.commandState.env

/--
`Lean.Environment.add` is now private, but exported as `lean_environment_add`.
We call it here via `@[extern]` with a mock implementation.
-/
@[extern "lean_environment_add"]
private opaque addToEnv (env : Environment) (_ : ConstantInfo) : Environment

/--
Import a configuration `.olean` (e.g., `lakefile.olean`).
Auxiliary definition for `importConfigFile`.
-/
def importConfigFileCore (olean : FilePath) (leanOpts : Options) : IO Environment := do
  /-
  We could import the olean together with its imports using one
  `importModules` call, but that would mean we pay for a full
  `finalizeImports` each time, which is linear in the number of imported
  constants and extension entries (in fact, it is paid two more times: when
  marking the `Environment` object as multi-threaded, and when releasing
  it). As most lakefiles use the same set of imports, we instead construct
  an `Environment` for it only once, and then apply the lakefile contents
  on top of it like the elaborator would. Thus the non-shared part of the
  `Environment` is very small.
  -/
  let (mod, _) ← readModuleData olean
  let mut env ← importModulesUsingCache mod.imports leanOpts 1024
  -- Apply constants (does not go through the kernel, so order is irrelevant)
  env := mod.constants.foldl addToEnv env
  /-
  Apply extension entries (`PersistentEnvExtension.addEntryFn` is pure and
  does not have access to the whole environment, so no dependency worries
  here either)
  -/
  let extDescrs ← persistentEnvExtensionsRef.get
  let extNameIdx ← mkExtNameMap 0
  for (extName, ents) in mod.entries do
    if let some entryIdx := extNameIdx.find? extName then
      for ent in ents do
        env := extDescrs[entryIdx]!.addEntry env ent
  return env

instance : ToJson Hash := ⟨(toJson ·.val)⟩
instance : FromJson Hash := ⟨((⟨·⟩) <$> fromJson? ·)⟩

structure ConfigTrace where
  platform : String
  leanHash : String
  configHash : Hash
  options : NameMap String
  deriving ToJson, FromJson

inductive ConfigLock
| olean (h : IO.FS.Handle)
| lean (h : IO.FS.Handle) (lakeOpts : NameMap String)

/--
Import the `.olean` for the configuration file if `reconfigure` is not set and
an up-to-date one exists (i.e., one with matching configuration and on the same
toolchain). Otherwise, elaborate the configuration and save it to the `.olean`.
-/
def importConfigFile (pkgDir lakeDir : FilePath) (lakeOpts : NameMap String)
(leanOpts := Options.empty) (configFile := pkgDir / defaultConfigFile) (reconfigure := true) : LogIO Environment := do
  let some configName := FilePath.mk <$> configFile.fileName
    | error "invalid configuration file name"
  let olean := lakeDir / configName.withExtension "olean"
  let traceFile := lakeDir / configName.withExtension "olean.trace"
  /-
  Remark: To prevent race conditions between the `.olean` and its trace file
  (i.e., one process writes a new configuration while another reads an old one
  and vice versa), Lake takes opens a single handle on the trace file and
  acquires a lock on it. The lock is held while the lock data is read and
  the olean is either imported or a new one is written with new lock data.
  -/
  let configHash ← computeTextFileHash configFile
  let configLock : ConfigLock ← id do
    let validateTrace h : IO ConfigLock := id do
      if reconfigure then
        h.lock; return .lean h lakeOpts
      h.lock (exclusive := false)
      let contents ← h.readToEnd; h.rewind
      let .ok (trace : ConfigTrace) := Json.parse contents >>= fromJson?
        | error "compiled configuration is invalid; run with `-R` to reconfigure"
      let upToDate := trace.platform = platformDescriptor ∧
        trace.leanHash = Lean.githash ∧ trace.configHash = configHash
      if upToDate then
        return .olean h
      else
        -- Upgrade to an exclusive lock
        let lockFile := lakeDir / configName.withExtension "olean.lock"
        let hLock ← IO.FS.Handle.mk lockFile .write
        hLock.lock; h.unlock; h.lock; hLock.unlock
        return .lean h trace.options
    if (← traceFile.pathExists) then
      validateTrace <| ← IO.FS.Handle.mk traceFile .readWrite
    else
      IO.FS.createDirAll lakeDir
      match (← IO.FS.Handle.mk traceFile .writeNew |>.toBaseIO) with
      | .ok h =>
        h.lock; return .lean h lakeOpts
      | .error (.alreadyExists ..) =>
        validateTrace <| ← IO.FS.Handle.mk traceFile .readWrite
      | .error e => error e.toString
  match configLock with
  | .olean h =>
    let env ← importConfigFileCore olean leanOpts
    h.unlock
    return env
  | .lean h lakeOpts =>
    let env ← elabConfigFile pkgDir lakeOpts leanOpts configFile
    Lean.writeModule env olean
    h.putStrLn <| Json.pretty <| toJson
      {platform := platformDescriptor, leanHash := Lean.githash,
        configHash, options := lakeOpts : ConfigTrace}
    h.truncate
    h.unlock
    return env
