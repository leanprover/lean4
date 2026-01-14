/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Util.Log
public import Lake.Load.Config
public import Lean.Environment
import Lean.Compiler.IR
import Lean.Elab.Frontend
import Lake.DSL.Extensions
import Lake.DSL.Attributes
import Lake.Load.Config
import Lake.Build.Trace
import Lake.Util.JsonObject

/-! # Lean Configuration Elaborator

This module contains the definitions to elaborate a Lake configuration file.
-/


open System Lean

namespace Lake

/- Cache for the imported header environment of Lake configuration files. -/
private builtin_initialize importEnvCache :
  IO.Ref (Std.HashMap (Array Import) Environment) ← IO.mkRef {}

/-- Like `importModules`, but fetch the resulting import state from the cache if possible. -/
public def importModulesUsingCache
  (imports : Array Import) (opts : Options) (trustLevel : UInt32)
: IO Environment := do
  if let some env := (← importEnvCache.get)[imports]? then
    return env
  let env ← importModules (loadExts := true) imports opts trustLevel
  importEnvCache.modify (·.insert imports env)
  return env

/-- Like `Lean.Elab.processHeader`, but using `importEnvCache`. -/
-- TODO: Update to incorporate the module system
private def processHeader
  (header : TSyntax ``Parser.Module.header) (opts : Options)
  (inputCtx : Parser.InputContext) : StateT MessageLog IO Environment
:= do
  try
    let imports := Elab.headerToImports header
    importModulesUsingCache imports opts 1024
  catch e =>
    let pos := inputCtx.fileMap.toPosition <| header.raw.getPos?.getD 0
    modify (·.add { fileName := inputCtx.fileName, data := toString e, pos })
    mkEmptyEnvironment

/-- Main module `Name` of a Lake configuration file. -/
public def configModuleName : Name := `lakefile

/-- Elaborate `configFile` with the given package directory and options. -/
def elabConfigFile
  (pkgIdx : Nat) (pkgName : Name) (pkgDir : FilePath) (lakeOpts : NameMap String)
  (leanOpts := Options.empty) (configFile := pkgDir / defaultLeanConfigFile)
: LogIO Environment := do

  -- Read file and initialize environment
  let input ← IO.FS.readFile configFile
  let inputCtx := Parser.mkInputContext input configFile.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header leanOpts inputCtx messages
  let env := env.setMainModule configModuleName

  -- Configure extensions
  let env := nameExt.setState env ⟨pkgIdx, pkgName⟩
  let env := dirExt.setState env pkgDir
  let env := optsExt.setState env lakeOpts

  -- Elaborate File
  let commandState := Elab.Command.mkState env messages leanOpts
  let s ← Elab.IO.processCommands inputCtx parserState commandState

  -- Log messages
  s.commandState.messages.forM (logMessage ·)

  -- Check result
  if s.commandState.messages.hasErrors then
    error s!"{configFile}: package configuration has errors"
  else
    return s.commandState.env

/--
`Lean.Kernel.Environment.add` is now private, this is an exported helper wrapping it for
`Lean.Environment`.
-/
@[extern "lake_environment_add"]
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
  let env ← importModulesUsingCache mod.imports leanOpts 1024
  -- Apply constants (does not go through the kernel, so order is irrelevant)
  let env := mod.constants.foldl addToEnv env
  /-
  Below, we pass module environment extension entries to
  `PersistentEnvExtension.addEntryFn` - but for an extension of
  non-erased type `PersistentEnvExtension α β σ`, the former are of type
  `α` while `addEntryFn` expects `β`s (the type-erased
  `persistentEnvExtensionsRef` ought to be `unsafe` to prevent this from
  simply compiling but it isn't right now). Fortunately, all extensions
  relevant for workspace loading, which we filter for here, have `α = β`;
  entries for any other extensions can safely be ignored.
  -/
  let extDescrs ← persistentEnvExtensionsRef.get
  let extNameIdx ← mkExtNameMap 0
  let env := mod.entries.foldl (init := env) fun env (extName, ents) =>
    if lakeExts.contains extName then
      match extNameIdx[extName]? with
      | some entryIdx =>
        -- Use `sync` to avoid `async` checks, which are not relevant here as there is only one
        -- environment branch.
        ents.foldl (extDescrs[entryIdx]!.addEntry (asyncMode := .sync)) env
      | none => env
    else
      env
  return env
where
  lakeExts :=
    NameSet.empty
    -- Lake Persistent Extensions
    |>.insert ``packageAttr
    |>.insert ``packageDepAttr
    |>.insert ``postUpdateAttr
    |>.insert ``scriptAttr
    |>.insert ``defaultScriptAttr
    |>.insert ``leanLibAttr
    |>.insert ``leanExeAttr
    |>.insert ``externLibAttr
    |>.insert ``targetAttr
    |>.insert ``defaultTargetAttr
    |>.insert ``testDriverAttr
    |>.insert ``lintDriverAttr
    |>.insert ``moduleFacetAttr
    |>.insert ``packageFacetAttr
    |>.insert ``libraryFacetAttr
    -- Docstring Extension (e.g., for scripts)
    |>.insert ``docStringExt
    -- IR Extension (for constant evaluation)
    |>.insert ``IR.declMapExt

structure ConfigTrace where
  idx : Nat
  name : Name
  platform : String
  leanHash : String
  configHash : Hash
  options : NameMap String
  deriving ToJson, FromJson

/--
Import the `.olean` for the configuration file if `reconfigure` is not set and
an up-to-date one exists (i.e., one with matching configuration and on the same
toolchain). Otherwise, elaborate the configuration and save it to the `.olean`.
-/
public def importConfigFile (cfg : LoadConfig) : LogIO Environment := do
  let some configName := FilePath.mk <$> cfg.configFile.fileName
    | error "invalid configuration file name"
  let pkgName := cfg.pkgName.toString (escape := false)
  let configDir := cfg.lakeDir / "config" / pkgName
  IO.FS.createDirAll configDir
  let olean := configDir / configName.withExtension "olean"
  let traceFile := configDir / configName.withExtension "olean.trace"
  let lockFile := configDir / configName.withExtension "olean.lock"
  /-
  Remark:
  To prevent race conditions between the `.olean` and its trace file
  (i.e., one process writes a new configuration while another reads an old one
  and vice versa), Lake performs file locking to ensure exclusive access.

  To check if the trace is up-to-date, Lake opens a read-only handle on the
  trace file and acquires a shared lock on it. The lock is held while the
  trace is read and compared to the expected value. If it matches, the olean is
  imported and the (shared) lock is then released.

  If the trace is out-of-date, Lake upgrades the trace to read-write handle
  with an exclusive lock. Lake does this by first acquiring an exclusive lock to
  configuration's lock file (i.e. `olean.lock`). While holding this lock, Lake
  releases the shared lock on the trace, re-opens the trace with a read-write
  handle, and acquires an exclusive lock on the trace. It then releases its
  lock on the lock file. writes the new lock data.
  -/
  let acquireTrace h : IO IO.FS.Handle := id do
    let hLock ← IO.FS.Handle.mk lockFile .write
    /-
    Remark:
    We do not wait for a lock here, because that can lead to deadlock.

    This is because we are already holding a shared lock on the trace.
    If multiple process race for this lock, one will get it and then
    wait for an exclusive lock on the trace file, but be blocked by the
    other process with a shared lock waiting on this file.

    While there is likely a way to sequence this to avoid erroring,
    simultaneous reconfigures are likely to produce unexpected results
    anyway, so the error seems wise nonetheless.
    -/
    if (← hLock.tryLock) then
      h.unlock
      let h ← IO.FS.Handle.mk traceFile .readWrite
      h.lock
      hLock.unlock
      return h
    else
      h.unlock
      error <| s!"could not acquire an exclusive configuration lock; " ++
        "another process may already be reconfiguring the package"
  let configHash ← computeTextFileHash cfg.configFile
  let elabConfig h (lakeOpts : NameMap String) : LogIO Environment := id do
    /-
    Remark:
    We write the trace before elaborating the configuration file
    to enable automatic reconfiguration on the next `lake` invocation if
    elaboration fails. To ensure a failure triggers a reconfigure, we must also
    remove any previous out-of-date `.olean`. Otherwise, Lake will treat the
    older `.olean` as matching the new trace.

    See the related PR and Zulip discussion for more details:
    [leanprover/lean4#3069](https://github.com/leanprover/lean4/pull/3069).
    -/
    match (← IO.FS.removeFile olean |>.toBaseIO) with
    | .ok _ | .error (.noFileOrDirectory ..) =>
      h.putStrLn <| Json.pretty <| toJson
        {platform := System.Platform.target, leanHash := cfg.lakeEnv.leanGithash,
          configHash, idx := cfg.pkgIdx, name := cfg.pkgName, options := lakeOpts : ConfigTrace}
      h.truncate
      let env ← elabConfigFile
        cfg.pkgIdx cfg.pkgName cfg.pkgDir lakeOpts cfg.leanOpts cfg.configFile
      Lean.writeModule env olean
      h.unlock
      return env
    | .error e => errorWithLog do
      logError <| toString e
      h.unlock
      IO.FS.removeFile traceFile
  let validateTrace h : LogIO Environment := id do
    if cfg.reconfigure then
      elabConfig (← acquireTrace h) cfg.lakeOpts
    else
      h.lock (exclusive := false)
      let contents ← h.readToEnd
      let errMsg := "compiled configuration is invalid; run with '-R' to reconfigure"
      match Json.parse contents with
      | .ok json =>
        match fromJson? json with
        | .ok (trace : ConfigTrace) =>
          let upToDate := (← olean.pathExists) ∧
            trace.idx = cfg.pkgIdx ∧ trace.name = cfg.pkgName ∧  trace.configHash = configHash ∧
            trace.platform = System.Platform.target ∧  trace.leanHash = cfg.lakeEnv.leanGithash
          if upToDate then
            let env ← importConfigFileCore olean cfg.leanOpts
            h.unlock
            return env
          else
            elabConfig (← acquireTrace h) trace.options
        | .error _ => -- trace has unexpected format, try to just read the one necessary field
          match JsonObject.fromJson? json >>= (·.get "options") with
          | .ok (opts : NameMap String) =>
            elabConfig (← acquireTrace h) opts
          | .error _ =>
            error errMsg
      | .error _ =>
        error errMsg
  if (← traceFile.pathExists) then
    validateTrace <| ← IO.FS.Handle.mk traceFile .read
  else
    IO.FS.createDirAll cfg.lakeDir
    match (← IO.FS.Handle.mk traceFile .writeNew |>.toBaseIO) with
    | .ok h =>
      h.lock; elabConfig h cfg.lakeOpts
    | .error (.alreadyExists ..) =>
      validateTrace <| ← IO.FS.Handle.mk traceFile .read
    | .error e => error e.toString
