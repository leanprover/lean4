/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Config.Cache
public import Lake.Config.Context
public import Lake.Build.Job.Basic

open System
namespace Lake

/-- Configuration options for a Lake build. -/
public structure BuildConfig extends LogConfig where
  /-- Whether to use modification times for trace checking. -/
  oldMode : Bool := false
  /-- Whether to trust `.hash` files. -/
  trustHash : Bool := true
  /-- Early exit if a target has to be rebuilt. -/
  noBuild : Bool := false
  /-- Verbosity level (`-q`, `-v`, or neither). -/
  verbosity : Verbosity := .normal
  /-- Whether to print a message when the build finishes successfully (if not quiet). -/
  showSuccess : Bool := false
  /-- File to save input-to-output mappings from the build of the workspace's root -/
  outputsFile? : Option FilePath := none
  /--
  Per-package Lean option overrides, applied to every module whose owning
  package's `baseName` appears as a key. When `recFetchSetup` builds module
  `M`, the `LeanOptions` associated with `M.pkg.baseName` (if any) are appended
  to `M.leanOptions`, overriding clashing entries.

  Used by `lake lint` to inject `linter.extra`/`linter.all` into every module
  of a target package (so transitively-imported first-party modules capture
  linter-tagged warnings), without touching dependencies.
  -/
  leanOptOverrides : Lean.NameMap Lean.LeanOptions := {}
  /--
  The miniumum OS version to target on MacOS.

  If a minimum is not set, linkers default the minimum to the host major version and
  will emit warnings if any lineed libraries (including system libraries) exceed the minium.
  Thus, the linker will complain when building on a system with an unset minimum and system
  libraries which require a higher minor version.

  ```
  ld64.lld: warning: /usr/lib/system/libsystem_kernel.dylib has version 13.5.0, which is newer than target minimum of 13.0.0
  ```

  To silence such warnings, Lake sets this far into the future by default (e.g., `99.0`).
  However, that itself can be wrong if a consumer of Lean library uses the minimum OS version
  to determine compatibility (e.g., Python does this). The far-flung version would then
  imply zero compatibility.

  In such cases, the desired deployment target can be manually specified . Depending on
  the desired scope, it can be set per-target, for all targets within a buld (with this),
  or across all builds with the environment variable `MACOSX_DEPLOYMENT_TARGET`.
  -/
  macosxDeploymentTarget? : Option String := none

/--
Whether the build should show progress information.

`Verbosity.quiet` hides progress and, for a `noBuild`,
`Verbosity.verbose` shows progress.
-/
public def BuildConfig.showProgress (cfg : BuildConfig) : Bool :=
  (cfg.noBuild ∧ cfg.verbosity == .verbose) ∨ cfg.verbosity != .quiet

/-- Mutable reference of registered build jobs. -/
@[expose] -- for codegen
public def JobQueue := IO.Ref (Array OpaqueJob)

/-- Returns a new empty job queue. -/
@[inline] public def mkJobQueue : BaseIO JobQueue :=
  IO.mkRef #[]

/-- A Lake context with a build configuration and additional build data. -/
public structure BuildContext extends BuildConfig, Context where
  leanTrace : BuildTrace
  registeredJobs : JobQueue
  /--
  Input-to-output(s) map for hashes of the root package's artifacts.
  If `none`, tracking outputs is disabled for this build.
  -/
  outputsRef? : Option CacheRef := none

/-- A transformer to equip a monad with a `BuildContext`. -/
public abbrev BuildT := ReaderT BuildContext

/-- A monad equipped with a Lake build context. -/
public abbrev MonadBuild (m : Type → Type u) :=
  MonadReaderOf BuildContext m

public instance [Pure m] : MonadLift LakeM (BuildT m) where
  monadLift x := fun ctx => pure <| x.run ctx.toContext

@[inline] public def getBuildContext [MonadBuild m] : m BuildContext :=
  readThe BuildContext

@[inline] public def getLeanTrace [Functor m] [MonadBuild m] : m BuildTrace :=
  (·.leanTrace) <$> getBuildContext

@[inline] public def getBuildConfig [Functor m] [MonadBuild m] : m BuildConfig :=
  (·.toBuildConfig) <$> getBuildContext

@[inline, inherit_doc BuildConfig.oldMode]
public def getIsOldMode [Functor m] [MonadBuild m] : m Bool :=
  (·.oldMode) <$> getBuildConfig

@[inline, inherit_doc BuildConfig.trustHash]
public def getTrustHash [Functor m] [MonadBuild m] : m Bool :=
  (·.trustHash) <$> getBuildConfig

@[inline, inherit_doc BuildConfig.noBuild]
public def getNoBuild [Functor m] [MonadBuild m] : m Bool :=
  (·.noBuild) <$> getBuildConfig

@[inline, inherit_doc BuildConfig.verbosity]
public def getVerbosity [Functor m] [MonadBuild m] : m Verbosity :=
  (·.verbosity) <$> getBuildConfig

@[inline] public def getIsVerbose [Functor m] [MonadBuild m] : m Bool :=
  (· == .verbose) <$> getVerbosity

@[inline] public def getIsQuiet [Functor m] [MonadBuild m] : m Bool :=
  (· == .quiet) <$> getVerbosity

@[inline, inherit_doc BuildConfig.leanOptOverrides]
public def getLeanOptOverrides [Functor m] [MonadBuild m]
    : m (Lean.NameMap Lean.LeanOptions) :=
  (·.leanOptOverrides) <$> getBuildConfig

@[inline, inherit_doc BuildConfig.macosxDeploymentTarget?]
public def getMacOSXDeploymentTarget? [Functor m] [MonadBuild m] : m (Option String) :=
  (·.macosxDeploymentTarget?) <$> getBuildConfig
